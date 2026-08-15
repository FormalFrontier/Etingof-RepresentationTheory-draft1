/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.DiscussionCharacterComputationSetup

#doc (Manual) "Setup for computing characters of U\\_lambda: conjugacy classes C\\_i and power sums H\\_m" =>

# Setup for computing characters of U\_lambda: conjugacy classes C\_i and power sums H\_m
%%%
tag := "Chapter5/Discussion_character_computation_setup"
number := false
%%%

Now let us compute the character of $`U_\lambda`. Let $`C_\mathbf{i}` be the conjugacy class in $`S_n` having $`i_m` cycles of length $`m` for all $`m \geq 1` (here $`\mathbf{i}` is a shorthand notation for $`(i_1, \ldots, i_m, \ldots)`). Also let $`x_1, \ldots, x_N` be variables, and let

$$`H_m(x) = \sum_j x_j^m`

be the power sum polynomials.

## Formalization
%%%
tag := "Chapter5/Discussion_character_computation_setup/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.PermutationPolynomialAuxiliary.partitionPermutationValue}

{Manual.docstring RepresentationTheory.PermutationPolynomialAuxiliary.permutationPolynomialAuxiliary}
