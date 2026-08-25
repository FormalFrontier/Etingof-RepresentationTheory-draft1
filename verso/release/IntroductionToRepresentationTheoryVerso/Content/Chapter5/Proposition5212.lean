/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Proposition5212

#doc (Manual) "Special values of Schur polynomials at geometric progressions" =>

# Special values of Schur polynomials at geometric progressions
%%%
tag := "Chapter5/Proposition5.21.2"
number := false
%%%

*Proposition 5.21.2.*

$$`S_\lambda(1, z, z^2, \ldots, z^{N-1}) = \prod_{1 \leq i < j \leq N} \frac{z^{\lambda_i - i} - z^{\lambda_j - j}}{z^{-i} - z^{-j}}.`

_Therefore,_

$$`S_\lambda(1, \ldots, 1) = \prod_{1 \leq i < j \leq N} \frac{\lambda_i - \lambda_j + j - i}{j - i}.`

*Proof.* First, $`D_\lambda(1, z, \ldots, z^{N-1})` is a Vandermonde determinant evaluated at $`(z^{\lambda_i + N - i})_{1 \leq i \leq N}`, so it equals $`\prod_{i < j} (z^{\lambda_i + N - i} - z^{\lambda_j + N - j})`. Dividing by the same formula with $`\lambda = 0` yields the formula for $`S_\lambda(1, z, \ldots, z^{N-1})`. Now take $`\lim_{z \to 1}` and apply L'Hopital's rule. $`\square`

## Formalization
%%%
tag := "Chapter5/Proposition5.21.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.PartitionPolynomialEvaluation.auxiliaryComplexInversePowerEvaluationFormula}

{Manual.docstring RepresentationTheory.PartitionPolynomialEvaluation.auxiliaryEvaluationAtOneFormula}

{Manual.docstring RepresentationTheory.PartitionPolynomialEvaluation.auxiliaryFieldEvaluationFormula}
