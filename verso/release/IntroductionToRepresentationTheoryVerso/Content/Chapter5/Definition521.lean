/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Definition521

#doc (Manual) "Algebraic number and algebraic integer via monic polynomials" =>

# Algebraic number and algebraic integer via monic polynomials
%%%
tag := "Chapter5/Definition5.2.1"
number := false
%%%
**Definition 5.2.1.** $`z \in \mathbb{C}` is an **algebraic number** (respectively, an **algebraic integer**) if $`z` is a root of a monic polynomial with rational (respectively, integer) coefficients.

## Formalization
%%%
tag := "Chapter5/Definition5.2.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.AlgebraicNumbers.PolynomialCriteria.isIntegral_iff_exists_monic_aeval_eq_zero}

### Supporting declarations

{Manual.docstring RepresentationTheory.AlgebraicNumbers.PolynomialCriteria.isAlgebraic_iff_exists_ne_zero_aeval_eq_zero}
