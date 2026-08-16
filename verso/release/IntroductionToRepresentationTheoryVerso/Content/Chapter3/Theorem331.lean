/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.Theorem331

#doc (Manual) "Irreducible representations of direct sums of matrix algebras" =>
# Irreducible representations of direct sums of matrix algebras
%%%
tag := "Chapter3/Theorem3.3.1"
number := false
%%%
**Theorem 3.3.1.** _Let $`A = \bigoplus_{i=1}^r \operatorname{Mat}_{d_i}(k)`. Then the irreducible representations of $`A` are $`V_1 = k^{d_1}, \ldots, V_r = k^{d_r}`, and any finite dimensional representation of $`A` is a direct sum of copies of $`V_1, \ldots, V_r`._

## Formalization
%%%
tag := "Chapter3/Theorem3.3.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Matrix.ProductSemisimplicity.exists_linearEquiv_directSum_standardModules}

{Manual.docstring RepresentationTheory.Algebra.Matrix.ProductSemisimplicity.simpleModule_linearEquiv_standardModule}

{Manual.docstring RepresentationTheory.Algebra.Matrix.ProductSemisimplicity.standardModule_equiv_imp_eq}

{Manual.docstring RepresentationTheory.Algebra.Matrix.ProductSemisimplicity.standardModule_isSimpleModule}
