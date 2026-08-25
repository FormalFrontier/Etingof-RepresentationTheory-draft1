/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Problem5125

#doc (Manual) "Find the sum of dimensions of all irreducible representations of S\\_n" =>

# Find the sum of dimensions of all irreducible representations of S\_n
%%%
tag := "Chapter5/Problem5.12.5"
number := false
%%%

**Problem 5.12.5.** Find the sum of dimensions of all irreducible representations of the symmetric group $`S_n`.

Hint: Show that all irreducible representations of $`S_n` are real, i.e., admit a nondegenerate invariant symmetric form. Then use the Frobenius-Schur theorem.

## Formalization
%%%
tag := "Chapter5/Problem5.12.5/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.SymmetricGroup.SimpleDimensions.sum_finrank_simple_eq_card_involutions}
