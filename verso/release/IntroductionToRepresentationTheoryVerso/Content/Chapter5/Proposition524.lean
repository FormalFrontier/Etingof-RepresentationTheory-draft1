/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Proposition524

#doc (Manual) "Algebraic integers form a ring; algebraic numbers form a field" =>

# Algebraic integers form a ring; algebraic numbers form a field
%%%
tag := "Chapter5/Proposition5.2.4"
number := false
%%%

**Proposition 5.2.4.** _(i) $`\overline{\mathbb{Z}}` is a ring._

_(ii) $`\overline{\mathbb{Q}}` is a field. Namely, it is an algebraic closure of the field of rational numbers._

**Proof.** We will be using Definition 5.2.2. Let $`\alpha` be an eigenvalue of

$$`\mathcal{A} \in \mathrm{Mat}_n(\mathbb{C})`

with eigenvector $`v`, and let $`\beta` be an eigenvalue of

$$`\mathcal{B} \in \mathrm{Mat}_m(\mathbb{C})`
with eigenvector $`w`. Then $`\alpha \pm \beta` is an eigenvalue of

$$`\mathcal{A} \otimes \mathrm{Id}_m \pm \mathrm{Id}_n \otimes \mathcal{B},`

and $`\alpha\beta` is an eigenvalue of

$$`\mathcal{A} \otimes \mathcal{B}.`

The corresponding eigenvector is in both cases $`v \otimes w`. This shows that both $`\overline{\mathbb{Z}}` and $`\overline{\mathbb{Q}}` are rings. To show that the latter is a field, it suffices to note that if $`\alpha \neq 0` is a root of a polynomial $`p(x)` of degree $`d`, then $`\alpha^{-1}` is a root of $`x^d p(1/x)`. The last statement is easy, since a number $`\alpha` is algebraic if and only if it defines a finite extension of $`\mathbb{Q}`. $`\square`

## Formalization
%%%
tag := "Chapter5/Proposition5.2.4/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.NumberTheory.AlgebraicNumber.Complex.distinguishedIntSubalgebra}

{Manual.docstring RepresentationTheory.NumberTheory.AlgebraicNumber.Complex.distinguishedRatIntermediateField}

{Manual.docstring RepresentationTheory.NumberTheory.AlgebraicNumber.Complex.isAlgClosure_rat_distinguishedRatIntermediateField}

### Supporting declarations

{Manual.docstring RepresentationTheory.NumberTheory.AlgebraicNumber.Complex.algebra_isAlgebraic_rat_distinguishedRatIntermediateField}

{Manual.docstring RepresentationTheory.NumberTheory.AlgebraicNumber.Complex.isAlgClosed_distinguishedRatIntermediateField}

{Manual.docstring RepresentationTheory.NumberTheory.AlgebraicNumber.Complex.isAlgebraic_rat_complex_add_mul_inv}

{Manual.docstring RepresentationTheory.NumberTheory.AlgebraicNumber.Complex.isIntegral_int_complex_add_mul}
