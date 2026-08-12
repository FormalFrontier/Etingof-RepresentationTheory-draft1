/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.DiscussionConcreteLieExamplesContinued

#doc (Manual) "Concrete Lie algebra examples (continued): aff(1), so(n)" =>
# Concrete Lie algebra examples (continued): aff(1), so(n)
%%%
tag := "Chapter2/Discussion_concrete_Lie_examples_continued"
number := false
%%%
(4) The algebra $`\operatorname{aff}(1)` of matrices $`\begin{pmatrix} * & * \\ 0 & 0 \end{pmatrix}`.
Its basis consists of $`X = \begin{pmatrix} 1 & 0 \\ 0 & 0 \end{pmatrix}` and $`Y = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix}`, with $`[X, Y] = Y`.

(5) $`\mathfrak{so}(n)`, the space of skew-symmetric $`n \times n` matrices, with $`[a, b] = ab - ba`.

## Formalization
%%%
tag := "Chapter2/Discussion_concrete_Lie_examples_continued/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.LieAlgebra.ModularRepresentations.bracket_eq}

{Manual.docstring RepresentationTheory.LieAlgebra.TwoByTwoMatrixAuxiliary.finrank_eq_two}

{Manual.docstring RepresentationTheory.LieAlgebra.TwoByTwoMatrixAuxiliary.matrixLieSubalgebraAux}

{Manual.docstring RepresentationTheory.LieAlgebra.TwoByTwoMatrixAuxiliary.matrixLieSubalgebrasAux_eq}

{Manual.docstring RepresentationTheory.LieAlgebra.TwoByTwoMatrixAuxiliary.subalgebraBasisAux}

{Manual.docstring RepresentationTheory.LieAlgebra.TwoByTwoMatrixAuxiliary.twoElementVector_linearIndependent}

{Manual.docstring RepresentationTheory.LieAlgebra.TwoByTwoMatrixAuxiliary.twoElementVector_span_eq_top}
