/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter4.Theorem4102

#doc (Manual) "Factorization of the Frobenius determinant" =>

# Factorization of the Frobenius determinant
%%%
tag := "Chapter4/Theorem4.10.2"
number := false
%%%

**Theorem 4.10.2.**

$$`\det X_G = \prod_{j=1}^{r} P_j(\mathbf{x})^{\deg P_j}`

_for some pairwise nonproportional irreducible polynomials $`P_j(\mathbf{x})`, where $`r` is the number of conjugacy classes of $`G`._

## Formalization
%%%
tag := "Chapter4/Theorem4.10.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.auxiliaryGroupPolynomial_eq_sign_smul_prod_auxiliaryPolynomial_pow}
