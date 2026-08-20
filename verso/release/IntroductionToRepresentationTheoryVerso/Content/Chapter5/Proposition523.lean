/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Proposition523

#doc (Manual) "Equivalence of Definitions 5.2.1 and 5.2.2" =>

# Equivalence of Definitions 5.2.1 and 5.2.2
%%%
tag := "Chapter5/Proposition5.2.3"
number := false
%%%
**Proposition 5.2.3.** _Definitions (5.2.1) and (5.2.2) are equivalent._

**Proof.** To show that the condition of Definition 5.2.2 implies the condition of Definition 5.2.1, notice that $`z` is a root of the characteristic polynomial of the matrix (a monic polynomial with rational, respectively integer, coefficients). To establish the converse, suppose $`z` is a root of

$$`p(x) = x^n + a_1 x^{n-1} + \ldots + a_{n-1} x + a_n.`

Then the characteristic polynomial of the following matrix (called the **companion matrix**) is $`p(x)`:

$$`\begin{pmatrix} 0 & 0 & 0 & \ldots & 0 & -a_n \\ 1 & 0 & 0 & \ldots & 0 & -a_{n-1} \\ 0 & 1 & 0 & \ldots & 0 & -a_{n-2} \\ & & & \vdots & & \\ 0 & 0 & 0 & \ldots & 1 & -a_1 \end{pmatrix}.`

Since $`z` is a root of the characteristic polynomial of this matrix, it is an eigenvalue of this matrix. $`\square`

## Formalization
%%%
tag := "Chapter5/Proposition5.2.3/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Polynomial.AdjoinRoot.Matrix.Complex.exists_int_monic_root_iff_exists_int_matrix_charpoly_root}

### Supporting declarations

{Manual.docstring RepresentationTheory.Polynomial.AdjoinRoot.Matrix.Complex.isAlgebraic_iff_isRoot_rat_matrix_charpoly}

{Manual.docstring RepresentationTheory.Polynomial.AdjoinRoot.Matrix.Complex.isRoot_int_matrix_charpoly_of_int_monic}

{Manual.docstring RepresentationTheory.Polynomial.AdjoinRoot.Matrix.Complex.isRoot_rat_matrix_charpoly_of_rat_monic}

{Manual.docstring RepresentationTheory.Polynomial.AdjoinRoot.Matrix.Polynomial.auxiliaryMatrix}

{Manual.docstring RepresentationTheory.Polynomial.AdjoinRoot.Matrix.Polynomial.charpoly_auxiliaryMatrix_eq_of_monic}

{Manual.docstring RepresentationTheory.Polynomial.AdjoinRoot.Matrix.Polynomial.isRoot_charpoly_map_auxiliaryMatrix_of_monic}
