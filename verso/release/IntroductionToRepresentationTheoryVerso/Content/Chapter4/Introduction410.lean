/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter4.Introduction410

#doc (Manual) "Section 4.10: Frobenius determinant \u2014 group determinant setup" =>

# Section 4.10: Frobenius determinant — group determinant setup
%%%
tag := "Chapter4/Introduction_4.10"
number := false
%%%

## 4.10. Frobenius determinant
%%%
tag := "Chapter4/Introduction_4.10/heading-1"
%%%

Enumerate the elements of a finite group $`G` as follows: $`g_1, g_2, \ldots, g_n`. Introduce $`n` variables indexed with the elements of $`G`:

$$`x_{g_1}, x_{g_2}, \ldots, x_{g_n}.`

## Formalization
%%%
tag := "Chapter4/Introduction_4.10/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.Group.IndexedPolynomial.groupIndexedPolynomial}
