/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.Remark315

#doc (Manual) "Generalization of Proposition 3.1.4 to non-algebraically-closed fields" =>
# Generalization of Proposition 3.1.4 to non-algebraically-closed fields
%%%
tag := "Chapter3/Remark3.1.5"
number := false
%%%
**Remark 3.1.5.** In Proposition 3.1.4, it is not important that $`k` is algebraically closed, nor does it matter that $`V` is finite dimensional. If these assumptions are dropped, the only change needed is that the entries of the matrix $`X_i` are no longer in $`k` but in $`D_i = \operatorname{End}_A(V_i)`, which is, as we know, a division algebra. The proof of this generalized version of Proposition 3.1.4 is the same as before (check it!).

## Formalization
%%%
tag := "Chapter3/Remark3.1.5/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Module.SimpleMatrixCoordinates.exists_equiv_directSum_fin}

{Manual.docstring RepresentationTheory.Algebra.Module.SimpleMatrixCoordinates.exists_injective_coordinates_directSum}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.Module.SimpleMatrixCoordinates.injective_iff_matrix_relation}

{Manual.docstring RepresentationTheory.Algebra.Module.SimpleMatrixCoordinates.linearIndependent_iff_matrix_relation}

{Manual.docstring RepresentationTheory.Algebra.Module.SimpleMatrixCoordinates.linearMapAddEquivMatrix}

{Manual.docstring RepresentationTheory.Algebra.Module.SimpleMatrixCoordinates.linearMapAddEquivMatrix_apply}

{Manual.docstring RepresentationTheory.Algebra.Module.SimpleMatrixCoordinates.nonempty_divisionRing_end}
