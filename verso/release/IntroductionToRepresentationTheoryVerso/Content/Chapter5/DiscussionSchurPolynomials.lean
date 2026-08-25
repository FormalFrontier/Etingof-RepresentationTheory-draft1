/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.DiscussionSchurPolynomials

#doc (Manual) "Definition of D\\_lambda and Schur polynomials S\\_lambda" =>

# Definition of D\_lambda and Schur polynomials S\_lambda
%%%
tag := "Chapter5/Discussion_Schur_polynomials"
number := false
%%%

Let $`\lambda = (\lambda_1, \ldots, \lambda_p)` be a partition of $`n`, and let $`N \geq p`. Let

$$`D_\lambda(x) = \sum_{s \in S_N} (-1)^s \prod_{j=1}^{N} x_{s(j)}^{\lambda_j + N - j} = \det(x_i^{\lambda_j + N - j}).`

Define the polynomials

$$`S_\lambda(x) := \frac{D_\lambda(x)}{D_0(x)}`

(clearly $`D_0(x)` is just $`\Delta(x)`). It is easy to see that these are indeed polynomials, as $`D_\lambda` is antisymmetric and therefore must be divisible by $`\Delta`. The polynomials $`S_\lambda` are called the *Schur polynomials*.

## Formalization
%%%
tag := "Chapter5/Discussion_Schur_polynomials/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial_mul_det_staircase}

### Supporting declarations

{Manual.docstring RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase}

{Manual.docstring RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix}

{Manual.docstring RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial}

{Manual.docstring RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents}
