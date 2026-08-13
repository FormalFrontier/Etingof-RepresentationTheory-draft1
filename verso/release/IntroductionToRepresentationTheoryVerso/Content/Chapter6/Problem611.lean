/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter6.Problem611

#doc (Manual) "Problem 6.1.1: Field embeddings" =>

# Problem 6.1.1: Field embeddings
%%%
tag := "Chapter6/Problem6.1.1"
number := false
%%%

*Problem 6.1.1.* Field embeddings. Recall that $`k(y_1, \ldots, y_m)` denotes the field of rational functions of $`y_1, \ldots, y_m` over a field $`k`. Let $`f : k[x_1, \ldots, x_n] \to k(y_1, \ldots, y_m)` be an injective $`k`-algebra homomorphism. Show that $`m \geq n`. (Look at the growth of dimensions of the spaces $`W_N` of polynomials of degree $`N` in $`x_i` and their images under $`f` as $`N \to \infty`.) Deduce that if $`f : k(x_1, \ldots, x_n) \to k(y_1, \ldots, y_m)` is a $`k`-linear field embedding, then $`m \geq n`.

## Formalization
%%%
tag := "Chapter6/Problem6.1.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.TranscendenceDegree.PolynomialFractionFields.numVariables_le_of_fractionRing_mvPolynomial_algHom}

{Manual.docstring RepresentationTheory.Algebra.TranscendenceDegree.PolynomialFractionFields.numVariables_le_of_injective_mvPolynomial_algHom_to_fractionRing}
