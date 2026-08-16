/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.Remark334

#doc (Manual) "Yet another proof of Theorem 3.3.1 using Lemma 3.1.6" =>
# Yet another proof of Theorem 3.3.1 using Lemma 3.1.6
%%%
tag := "Chapter3/Remark3.3.4"
number := false
%%%
**Remark 3.3.4.** Here is yet another proof of Theorem 3.3.1, using Lemma 3.1.6. Let $`X` be an $`n`-dimensional representation of $`A`. Let $`\{x_1, \ldots, x_n\}` be a basis of $`X`. Then there is a unique homomorphism $`\psi : A^n \to X` such that $`\psi(a_1, \ldots, a_n) = \sum_i a_i x_i`, and it is surjective. Hence $`X` is a quotient of $`A^n`. But we have seen that $`A = \bigoplus_{i=1}^r d_i V_i`,
hence $`A^n = \bigoplus_{i=1}^r n d_i V_i` as a representation of $`A`. Thus by Lemma 3.1.6, $`X = \bigoplus_{i=1}^r m_i V_i`, as desired.

## Formalization
%%%
tag := "Chapter3/Remark3.3.4/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Matrix.ProductSemisimplicity.exists_linearEquiv_directSum_standardModules}

{Manual.docstring RepresentationTheory.Algebra.Matrix.ProductSemisimplicity.matrixProductLinearEquivDirectSumColumns}

{Manual.docstring RepresentationTheory.Algebra.Matrix.ProductSemisimplicity.piMatrixProductLinearEquivDirectSum}

{Manual.docstring RepresentationTheory.Algebra.Module.BasisExpansion.basisExpansion}

{Manual.docstring RepresentationTheory.Algebra.Module.BasisExpansion.basisExpansion_apply}

{Manual.docstring RepresentationTheory.Algebra.Module.BasisExpansion.basisExpansion_surjective}

{Manual.docstring RepresentationTheory.Algebra.Module.BasisExpansion.eq_basisExpansion_of_apply}

{Manual.docstring RepresentationTheory.Algebra.Module.BasisExpansion.quotientKerBasisExpansionEquiv}
