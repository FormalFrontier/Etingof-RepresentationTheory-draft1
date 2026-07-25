import EtingofRepresentationTheory.Chapter9.Corollary9_7_3
import EtingofRepresentationTheory.Chapter9.Theorem9_6_4
import EtingofRepresentationTheory.Chapter9.Introduction_9_6
import EtingofRepresentationTheory.Chapter9.Exercise9_6_3
import EtingofRepresentationTheory.Infrastructure.BasicAlgebraExistence
import EtingofRepresentationTheory.Infrastructure.MoritaFGRestriction

/-!
# Corollary 9.7.3(i), categorical input form

The book's Corollary 9.7.3(i) is stated for an abstract `k`-linear finite abelian
category `𝒞`: any such `𝒞` is equivalent to the finite-dimensional modules over a unique
basic algebra `B(𝒞)`. The main development in `Corollary9_7_3.lean` formalizes the
algebra version (input = a finite-dimensional algebra `A`). This file records the
categorical input form: the input is an abstract `IsFiniteAbelianCategory`, and the
output packages both the Morita equivalence with a concrete finite-dimensional algebra
and the existence of a basic algebra Morita equivalent to it.

## What is proved here

`Etingof.Corollary_9_7_3_i_categorical`: for a `k`-linear finite abelian category `𝒞`
over an algebraically closed field `k`, there are a progenerator `P` of `𝒞` and a basic
`k`-algebra `B` such that

* `𝒞 ≌ FGModuleCat (End P)ᵐᵒᵖ` (Theorem 9.6.4), and
* `(End P)ᵐᵒᵖ` is Morita equivalent to `B` (Corollary 9.7.3(i), algebra version).

Here `(End P)ᵐᵒᵖ` is the finite-dimensional algebra `A` whose finite-dimensional
modules realize `𝒞`. Because `End P = Hom(P, P)` is finite dimensional over `k` in a
`k`-linear finite abelian category (Etingof §9.6, "check it!"), so is `(End P)ᵐᵒᵖ`.

## The progenerator

The book asserts that every finite abelian category has a projective generator, and
`Etingof.Exercise963.exists_progenerator` (Exercise 9.6.3) proves it: the direct sum of
the projective covers of the finitely many simple objects is a progenerator. The public
theorems below quantify only over `𝒞` and choose `P` internally through that theorem.
Since the algebra `(End P)ᵐᵒᵖ` realizing `𝒞` depends on the choice, `P` reappears as an
existential in the conclusions that mention it. Each public statement has an
`_of_progenerator` variant taking `P` as a hypothesis, matching how Theorem 9.6.4 is
stated; those are the forms to use when a specific progenerator is already at hand.

## The single-equivalence form

The book's single conclusion `𝒞 ≌ B-fmod` combines the two conjuncts above into
one equivalence `𝒞 ≌ FGModuleCat B`. This requires restricting the Morita
equivalence `ModuleCat (End P)ᵐᵒᵖ ≌ ModuleCat B` (which `Etingof.MoritaEquivalent`
records at the level of the full module categories) to the finitely generated
subcategories, i.e. proving that a Morita equivalence preserves and reflects finite
generation of modules. Over the finite-dimensional algebras at hand this is the
statement that the equivalence preserves finite `k`-dimension; the general
categorical fact (a Morita equivalence sends f.g. modules to f.g. modules) is not
in Mathlib and uses the "finite epi from a generator onto a finitely
generated object" step. The combined statement is
`Etingof.Corollary_9_7_3_i_categorical_fgModule` below.
-/

open CategoryTheory

universe v u

/-- **Corollary 9.7.3(i), categorical input form, for a chosen progenerator.** The variant of
`Etingof.Corollary_9_7_3_i_categorical` that takes the progenerator as a hypothesis instead of
choosing one internally. Let `𝒞` be a `k`-linear finite abelian category over an algebraically
closed field `k`, and let `P` be a progenerator of `𝒞`. Then there is a basic `k`-algebra `B`
such that `𝒞` is equivalent to the finite-dimensional `(End P)ᵐᵒᵖ`-modules, and `(End P)ᵐᵒᵖ`,
a finite-dimensional `k`-algebra, is Morita equivalent to `B`.

The finite-dimensional algebra `A = (End P)ᵐᵒᵖ` whose finite-dimensional modules realize
`𝒞` comes from Theorem 9.6.4 (`Etingof.Theorem_9_6_4_corollary`); the basic algebra `B`
Morita equivalent to it comes from the algebra version of Corollary 9.7.3(i)
(`Etingof.exists_basic_morita_equivalent`).
(Etingof Corollary 9.7.3(i), categorical form) -/
theorem Etingof.Corollary_9_7_3_i_categorical_of_progenerator
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

/-- **Corollary 9.7.3(i), categorical input form.** This form yields the two facts
separately; for the single equivalence `𝒞 ≌ FGModuleCat B` see
`Etingof.Corollary_9_7_3_i_categorical_fgModule`. Let `𝒞` be a `k`-linear finite abelian
category over an algebraically closed field `k`. Then `𝒞` has a progenerator `P`, and there
is a basic `k`-algebra `B` such that `𝒞` is equivalent to the finite-dimensional
`(End P)ᵐᵒᵖ`-modules, and `(End P)ᵐᵒᵖ`, a finite-dimensional `k`-algebra, is Morita
equivalent to `B`.

Unlike `Etingof.Corollary_9_7_3_i_categorical_of_progenerator`, the progenerator is not asked
of the caller: it is produced by `Etingof.Exercise963.exists_progenerator` (Exercise 9.6.3).
It stays visible as an existential only because the realizing algebra `(End P)ᵐᵒᵖ` is defined
in terms of it.
(Etingof Corollary 9.7.3(i), categorical form) -/
theorem Etingof.Corollary_9_7_3_i_categorical
    {k : Type v} [Field k] [IsAlgClosed k]
    (C : Type u) [Category.{v} C]
    [Etingof.IsFiniteAbelianCategory C] [Linear k C]
    [Etingof.IsFiniteAbelianCategoryOverField k C] :
    ∃ (P : C) (_ : Etingof.IsProgenerator P) (B : Type v) (_ : Ring B) (_ : Algebra k B)
        (_ : Module.Finite k B),
      Etingof.IsBasicAlgebra k B ∧
        Nonempty (C ≌ FGModuleCat.{v} (End P)ᵐᵒᵖ) ∧
          Etingof.MoritaEquivalent (End P)ᵐᵒᵖ B := by
  -- Exercise 9.6.3: every finite abelian category has a progenerator.
  obtain ⟨P, ⟨hp⟩⟩ := Etingof.Exercise963.exists_progenerator C
  haveI : Etingof.IsProgenerator P := hp
  obtain ⟨B, instR, instA, instF, hbasic, hcat, hmor⟩ :=
    Etingof.Corollary_9_7_3_i_categorical_of_progenerator (k := k) C P
  exact ⟨P, hp, B, instR, instA, instF, hbasic, hcat, hmor⟩

/-- **Corollary 9.7.3(i), categorical input form, single equivalence, for a chosen
progenerator.** The variant of `Etingof.Corollary_9_7_3_i_categorical_fgModule` that takes the
progenerator as a hypothesis instead of choosing one internally. The two conjuncts of
`Etingof.Corollary_9_7_3_i_categorical_of_progenerator`
(`𝒞 ≌ FGModuleCat (End P)ᵐᵒᵖ` and `(End P)ᵐᵒᵖ` Morita equivalent to a basic `B`) are
combined into the single book statement `𝒞 ≌ FGModuleCat B` with `B` basic.

Let `𝒞` be a `k`-linear finite abelian category over an algebraically closed field `k`
with a progenerator `P`. Then there is a basic `k`-algebra `B` such that `𝒞` is equivalent
to the category of finite-dimensional `B`-modules.

The Morita equivalence `(End P)ᵐᵒᵖ ≌ B` restricts to the finitely generated module
subcategories via `Etingof.MoritaEquivalent.fgModuleCatEquiv`, and composing with
Theorem 9.6.4's `𝒞 ≌ FGModuleCat (End P)ᵐᵒᵖ` gives the single equivalence.
(Etingof Corollary 9.7.3(i), categorical form) -/
theorem Etingof.Corollary_9_7_3_i_categorical_fgModule_of_progenerator
    {k : Type v} [Field k] [IsAlgClosed k]
    (C : Type u) [Category.{v} C]
    [Etingof.IsFiniteAbelianCategory C] [Linear k C]
    [Etingof.IsFiniteAbelianCategoryOverField k C]
    (P : C) [hp : Etingof.IsProgenerator P] :
    ∃ (B : Type v) (_ : Ring B) (_ : Algebra k B) (_ : Module.Finite k B),
      Etingof.IsBasicAlgebra k B ∧ Nonempty (C ≌ FGModuleCat.{v} B) := by
  haveI : FiniteDimensional k (End P) :=
    @Etingof.IsFiniteAbelianCategoryOverField.finiteDimensional_hom k _ C _ _ _ _ P P
  haveI : Module.Finite k (End P)ᵐᵒᵖ := inferInstance
  have hcat : Nonempty (C ≌ FGModuleCat.{v} (End P)ᵐᵒᵖ) :=
    Etingof.Theorem_9_6_4_corollary (k := k) C P
  obtain ⟨B, instR, instA, instF, hbasic, hmor⟩ :=
    Etingof.exists_basic_morita_equivalent k (End P)ᵐᵒᵖ
  obtain ⟨eFG⟩ := Etingof.MoritaEquivalent.fgModuleCatEquiv hmor
  obtain ⟨eC⟩ := hcat
  exact ⟨B, instR, instA, instF, hbasic, ⟨eC.trans eFG⟩⟩

/-- **Corollary 9.7.3(i), categorical input form, single equivalence.** The book's statement:
any `k`-linear finite abelian category `𝒞` over an algebraically closed field `k` is the
category of finite-dimensional modules over a basic `k`-algebra `B`.

The progenerator needed to produce `B` is chosen internally, via
`Etingof.Exercise963.exists_progenerator` (Exercise 9.6.3); it does not appear in the
statement at all. For the uniqueness of `B` see
`Etingof.Corollary_9_7_3_i_categorical_strong`.
(Etingof Corollary 9.7.3(i), categorical form) -/
theorem Etingof.Corollary_9_7_3_i_categorical_fgModule
    {k : Type v} [Field k] [IsAlgClosed k]
    (C : Type u) [Category.{v} C]
    [Etingof.IsFiniteAbelianCategory C] [Linear k C]
    [Etingof.IsFiniteAbelianCategoryOverField k C] :
    ∃ (B : Type v) (_ : Ring B) (_ : Algebra k B) (_ : Module.Finite k B),
      Etingof.IsBasicAlgebra k B ∧ Nonempty (C ≌ FGModuleCat.{v} B) := by
  obtain ⟨P, ⟨hp⟩⟩ := Etingof.Exercise963.exists_progenerator C
  haveI : Etingof.IsProgenerator P := hp
  exact Etingof.Corollary_9_7_3_i_categorical_fgModule_of_progenerator (k := k) C P

/-- **Corollary 9.7.3(i), categorical input form, with uniqueness, for a chosen progenerator.**
The variant of `Etingof.Corollary_9_7_3_i_categorical_strong` that takes the progenerator as a
hypothesis instead of choosing one internally, and the strong form of
`Etingof.Corollary_9_7_3_i_categorical_fgModule_of_progenerator`: for a `k`-linear finite abelian
category `𝒞` over an algebraically closed field with a progenerator `P`, the basic algebra `B`
realizing
`𝒞 ≌ FGModuleCat B` is basic in both senses (`IsBasicAlgebraSplit` and the book's literal
`IsBasicAlgebra`), is `k`-linearly Morita equivalent to the endomorphism algebra
`A = (End P)ᵐᵒᵖ` of the progenerator, satisfies `dim B ≤ dim A`, and is unique up to
`k`-algebra isomorphism among basic algebras `k`-linearly Morita equivalent to `A`.

## Why uniqueness is stated relative to `(End P)ᵐᵒᵖ`

The book phrases uniqueness as "`B(𝒞)` is unique", i.e. relative to `𝒞` itself: any basic `B'`
with `𝒞 ≌ B'`-fmod is isomorphic to `B`. Deriving that form from this one needs the converse
of `Etingof.MoritaEquivalent.fgModuleCatEquiv` — an equivalence `FGModuleCat A ≌ FGModuleCat B'`
of the finitely generated subcategories has to be promoted back to a `k`-linear Morita
equivalence `ModuleCat A ≌ ModuleCat B'` of the full module categories, which the project does
not yet have (it is the subject of the open converse-bridge item on `Definition 9.7.1`).
Uniqueness relative to `A = (End P)ᵐᵒᵖ` is what the available machinery supports, and it is the
whole content once that converse bridge lands, since `𝒞 ≌ FGModuleCat A` by Theorem 9.6.4.
(Etingof Corollary 9.7.3(i), categorical form) -/
theorem Etingof.Corollary_9_7_3_i_categorical_strong_of_progenerator
    {k : Type v} [Field k] [IsAlgClosed k]
    (C : Type u) [Category.{v} C]
    [Etingof.IsFiniteAbelianCategory C] [Linear k C]
    [Etingof.IsFiniteAbelianCategoryOverField k C]
    (P : C) [hp : Etingof.IsProgenerator P] :
    ∃ (B : Type v) (_ : Ring B) (_ : Algebra k B) (_ : Module.Finite k B),
      Etingof.IsBasicAlgebraSplit.{v, v, v} k B ∧
        Etingof.IsBasicAlgebra k B ∧
          Nonempty (C ≌ FGModuleCat.{v} B) ∧
            Etingof.KLinearMoritaEquivalent k (End P)ᵐᵒᵖ B ∧
              Module.finrank k B ≤ Module.finrank k (End P)ᵐᵒᵖ ∧
                ∀ (B' : Type v) (_ : Ring B') (_ : Algebra k B') (_ : Module.Finite k B'),
                  Etingof.IsBasicAlgebra k B' →
                  Etingof.KLinearMoritaEquivalent k (End P)ᵐᵒᵖ B' →
                    Nonempty (B' ≃ₐ[k] B) := by
  haveI : FiniteDimensional k (End P) :=
    @Etingof.IsFiniteAbelianCategoryOverField.finiteDimensional_hom k _ C _ _ _ _ P P
  haveI : Module.Finite k (End P)ᵐᵒᵖ := inferInstance
  -- Theorem 9.6.4: `𝒞 ≌ FGModuleCat (End P)ᵐᵒᵖ`.
  obtain ⟨eC⟩ := Etingof.Theorem_9_6_4_corollary (k := k) C P
  -- The bundled algebra version applied to `A = (End P)ᵐᵒᵖ`.
  obtain ⟨B, instR, instA, instF, hsplit, hbasic, hmor, hdim, huniq⟩ :=
    Etingof.Corollary_9_7_3 k (End P)ᵐᵒᵖ
  -- Restrict the Morita equivalence to the finitely generated subcategories and compose.
  obtain ⟨eFG⟩ := Etingof.MoritaEquivalent.fgModuleCatEquiv hmor.toMoritaEquivalent
  exact ⟨B, instR, instA, instF, hsplit, hbasic, ⟨eC.trans eFG⟩, hmor, hdim, huniq⟩

/-- **Corollary 9.7.3(i), categorical input form, with uniqueness.** The strong form of
`Etingof.Corollary_9_7_3_i_categorical_fgModule`: a `k`-linear finite abelian category `𝒞` over
an algebraically closed field has a progenerator `P`, and the basic algebra `B` realizing
`𝒞 ≌ FGModuleCat B` is basic in both senses (`IsBasicAlgebraSplit` and the book's literal
`IsBasicAlgebra`), is `k`-linearly Morita equivalent to the endomorphism algebra
`A = (End P)ᵐᵒᵖ`, satisfies `dim B ≤ dim A`, and is unique up to `k`-algebra isomorphism among
basic algebras `k`-linearly Morita equivalent to `A`.

The progenerator is produced by `Etingof.Exercise963.exists_progenerator` (Exercise 9.6.3)
rather than asked of the caller; it remains an existential because uniqueness is stated
relative to `(End P)ᵐᵒᵖ`, for the reason recorded in
`Etingof.Corollary_9_7_3_i_categorical_strong_of_progenerator`.
(Etingof Corollary 9.7.3(i), categorical form) -/
theorem Etingof.Corollary_9_7_3_i_categorical_strong
    {k : Type v} [Field k] [IsAlgClosed k]
    (C : Type u) [Category.{v} C]
    [Etingof.IsFiniteAbelianCategory C] [Linear k C]
    [Etingof.IsFiniteAbelianCategoryOverField k C] :
    ∃ (P : C) (_ : Etingof.IsProgenerator P) (B : Type v) (_ : Ring B) (_ : Algebra k B)
        (_ : Module.Finite k B),
      Etingof.IsBasicAlgebraSplit.{v, v, v} k B ∧
        Etingof.IsBasicAlgebra k B ∧
          Nonempty (C ≌ FGModuleCat.{v} B) ∧
            Etingof.KLinearMoritaEquivalent k (End P)ᵐᵒᵖ B ∧
              Module.finrank k B ≤ Module.finrank k (End P)ᵐᵒᵖ ∧
                ∀ (B' : Type v) (_ : Ring B') (_ : Algebra k B') (_ : Module.Finite k B'),
                  Etingof.IsBasicAlgebra k B' →
                  Etingof.KLinearMoritaEquivalent k (End P)ᵐᵒᵖ B' →
                    Nonempty (B' ≃ₐ[k] B) := by
  obtain ⟨P, ⟨hp⟩⟩ := Etingof.Exercise963.exists_progenerator C
  haveI : Etingof.IsProgenerator P := hp
  obtain ⟨B, instR, instA, instF, hsplit, hbasic, hequiv, hmor, hdim, huniq⟩ :=
    Etingof.Corollary_9_7_3_i_categorical_strong_of_progenerator (k := k) C P
  exact ⟨P, hp, B, instR, instA, instF, hsplit, hbasic, hequiv, hmor, hdim, huniq⟩

/-- **Corollary 9.7.3(i), algebra version, book-faithful `fmod` form.** Any
finite-dimensional algebra `A` over an algebraically closed field `k` is Morita equivalent
(in the book's sense, on finite-dimensional/finitely generated modules) to some basic
algebra `B`.

This is `Etingof.Corollary_9_7_3_i` with its conclusion transported along the forward
reconciliation `Etingof.MoritaEquivalent.toFmod` to the literal book notion
`Etingof.MoritaEquivalentFmod`.
(Etingof Corollary 9.7.3(i), algebra version) -/
theorem Etingof.Corollary_9_7_3_i_fmod
    {k : Type v} [Field k] [IsAlgClosed k]
    (A : Type v) [Ring A] [Algebra k A] [Module.Finite k A] :
    ∃ (B : Type v) (_ : Ring B) (_ : Algebra k B) (_ : Module.Finite k B),
      Etingof.IsBasicAlgebra k B ∧ Etingof.MoritaEquivalentFmod A B := by
  obtain ⟨B, instR, instA, instF, hbasic, hmor⟩ := Etingof.Corollary_9_7_3_i k A
  exact ⟨B, instR, instA, instF, hbasic, hmor.toFmod⟩
