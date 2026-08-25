/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Remark5152

#doc (Manual) "Equivalent formulation of Theorem 5.15.1 using Laurent polynomials" =>

# Equivalent formulation of Theorem 5.15.1 using Laurent polynomials
%%%
tag := "Chapter5/Remark5.15.2"
number := false
%%%

*Remark 5.15.2.* Here is an equivalent formulation of Theorem 5.15.1: $`\chi_{V_\lambda}(C_\mathbf{i})` is the coefficient of $`x^\lambda` in the (Laurent) polynomial

$$`\prod_{i < j} \left(1 - \frac{x_j}{x_i}\right) \prod_{m \geq 1} H_m(x)^{i_m}.`

## Formalization
%%%
tag := "Chapter5/Remark5.15.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.IndexedTarget.Operations.partitionPermutation_eq_complexValue}

### Supporting declarations

{Manual.docstring RepresentationTheory.IndexedTarget.Operations.complexValue_eq_signed_coeff}

{Manual.docstring RepresentationTheory.IndexedTarget.Operations.integralExponentElement_mul_indexedTargetElement}
