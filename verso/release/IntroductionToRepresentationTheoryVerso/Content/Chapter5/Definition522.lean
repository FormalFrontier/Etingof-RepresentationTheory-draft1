/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Definition522

#doc (Manual) "Algebraic number and algebraic integer via eigenvalues of matrices" =>

# Algebraic number and algebraic integer via eigenvalues of matrices
%%%
tag := "Chapter5/Definition5.2.2"
number := false
%%%
**Definition 5.2.2.** $`z \in \mathbb{C}` is an **algebraic number**, (respectively, an **algebraic integer**), if $`z` is an eigenvalue of a matrix with rational (respectively, integer) entries.

## Formalization
%%%
tag := "Chapter5/Definition5.2.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.AlgebraicNumbers.MatrixCriteria.isAlgebraic_iff_exists_rat_matrix_charpoly_isRoot}

{Manual.docstring RepresentationTheory.AlgebraicNumbers.MatrixCriteria.isIntegral_iff_exists_int_matrix_charpoly_isRoot}
