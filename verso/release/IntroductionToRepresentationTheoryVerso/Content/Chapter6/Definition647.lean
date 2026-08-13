/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter6.Definition647

#doc (Manual) "Definition 6.4.7: Positive and negative roots" =>

# Definition 6.4.7: Positive and negative roots
%%%
tag := "Chapter6/Definition6.4.7"
number := false
%%%

*Definition 6.4.7.* We call a root $`\alpha = \sum_i k_i \alpha_i` a *positive root* if all $`k_i \geq 0`. A root for which $`k_i \leq 0` for all $`i` is called a *negative root*.

## Formalization
%%%
tag := "Chapter6/Definition6.4.7/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorCondition}

{Manual.docstring RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorPredicate}
