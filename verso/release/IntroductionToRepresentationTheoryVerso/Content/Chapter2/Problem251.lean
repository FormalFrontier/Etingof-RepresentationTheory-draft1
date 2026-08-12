/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Problem251

#doc (Manual) "Indecomposable quotient representation of polynomial algebra" =>
# Indecomposable quotient representation of polynomial algebra
%%%
tag := "Chapter2/Problem2.5.1"
number := false
%%%
**Problem 2.5.1.** Let $`A = k[x_1, \ldots, x_n]` and let $`I \neq A` be any ideal in $`A` containing all homogeneous polynomials of degree $`\geq N`. Show that $`A/I` is an indecomposable representation of $`A`.

## Formalization
%%%
tag := "Chapter2/Problem2.5.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.MvPolynomial.QuotientProperty.quotient_property_of_low_degree_homogeneous_mem}
