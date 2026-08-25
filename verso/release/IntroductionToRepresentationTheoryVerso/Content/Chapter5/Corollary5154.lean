/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Corollary5154

#doc (Manual) "Cauchy identity: R(x,y) as determinant and coefficient of x^\\{lambda+rho\\} y^\\{lambda+rho\\} is 1" =>

# Cauchy identity: R(x,y) as determinant and coefficient of x^\{lambda+rho\} y^\{lambda+rho\} is 1
%%%
tag := "Chapter5/Corollary5.15.4"
number := false
%%%

*Corollary 5.15.4* (Cauchy identity).

$$`R(x, y) = \det\left(\frac{1}{1 - x_i y_j}\right) = \sum_{\sigma \in S_N} \frac{(-1)^\sigma}{\prod_{j=1}^N (1 - x_j y_{\sigma(j)})}.`

Corollary 5.15.4 easily implies that the coefficient of $`x^{\lambda+\rho} y^{\lambda+\rho}` is 1. Indeed, if $`\sigma \neq 1` is a permutation in $`S_N`, the coefficient of this monomial in $`\prod_j \frac{1}{(1 - x_j y_{\sigma(j)})}` is obviously zero, since the coordinates of $`\lambda + \rho` are strictly decreasing and hence distinct. $`\square`

## Formalization
%%%
tag := "Chapter5/Corollary5.15.4/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.LinearAlgebra.AuxiliaryPowerSeriesMatrix.det_auxiliaryPowerSeriesMatrix}
