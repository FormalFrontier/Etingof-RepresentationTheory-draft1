/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.Example356

#doc (Manual) "Radicals of k\\[x\\]/(x^n) and upper triangular matrices" =>
# Radicals of k\[x\]/(x^n) and upper triangular matrices
%%%
tag := "Chapter3/Example3.5.6"
number := false
%%%
**Example 3.5.6.** 1. Let $`A = k[x]/(x^n)`. This algebra has a unique irreducible representation, which is a 1-dimensional space $`k`, in which $`x` acts by zero. So the radical $`\operatorname{Rad}(A)` is the ideal $`(x)`.

2. Let $`A` be the algebra of upper triangular $`n \times n` matrices. It is easy to check that the irreducible representations of $`A` are $`V_i`, $`i = 1, \ldots, n`, which are 1-dimensional, and any matrix $`x` acts by $`x_{ii}`. So the radical $`\operatorname{Rad}(A)` is the ideal of strictly upper triangular matrices (as it is a nilpotent ideal and contains the radical). A similar result holds for block-triangular matrices.

## Formalization
%%%
tag := "Chapter3/Example3.5.6/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.SimpleModule.MatrixAndTruncatedPolynomial.exists_equiv_finiteIndexAuxiliaryType}

{Manual.docstring RepresentationTheory.Algebra.SimpleModule.MatrixAndTruncatedPolynomial.finiteIndexAuxiliaryType.smul_eq_diagonalEntry_mul}

{Manual.docstring RepresentationTheory.Algebra.SimpleModule.MatrixAndTruncatedPolynomial.finrank_fieldNatAuxiliaryType}

{Manual.docstring RepresentationTheory.Algebra.SimpleModule.MatrixAndTruncatedPolynomial.finrank_finiteIndexAuxiliaryType}

{Manual.docstring RepresentationTheory.Algebra.SimpleModule.MatrixAndTruncatedPolynomial.isSimpleModule_fieldNatAuxiliaryType}

{Manual.docstring RepresentationTheory.Algebra.SimpleModule.MatrixAndTruncatedPolynomial.isSimpleModule_finiteIndexAuxiliaryType}

{Manual.docstring RepresentationTheory.Algebra.SimpleModule.MatrixAndTruncatedPolynomial.jacobson_auxiliaryMatrixSubalgebra}

{Manual.docstring RepresentationTheory.Algebra.SimpleModule.MatrixAndTruncatedPolynomial.jacobson_eq_span_root}

{Manual.docstring RepresentationTheory.Algebra.SimpleModule.MatrixAndTruncatedPolynomial.nonempty_equiv_fieldNatAuxiliaryType}

{Manual.docstring RepresentationTheory.Algebra.SimpleModule.MatrixAndTruncatedPolynomial.not_nonempty_equiv_finiteIndexAuxiliaryType}

{Manual.docstring RepresentationTheory.Algebra.SimpleModule.MatrixAndTruncatedPolynomial.root_smul_fieldNatAuxiliaryType}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.SimpleModule.MatrixAndTruncatedPolynomial.fieldNatAuxiliaryType}

{Manual.docstring RepresentationTheory.Algebra.SimpleModule.MatrixAndTruncatedPolynomial.finiteIndexAuxiliaryType}
