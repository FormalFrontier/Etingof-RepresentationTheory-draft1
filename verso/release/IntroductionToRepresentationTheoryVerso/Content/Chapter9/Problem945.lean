/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter9.Problem945

#doc (Manual) "Cartan matrix determinant and homological dimension" =>

# Cartan matrix determinant and homological dimension
%%%
tag := "Chapter9/Problem9.4.5"
number := false
%%%

*Problem 9.4.5.* (i) Show that if a finite dimensional algebra $`A` has finite homological dimension $`d` and if $`C` is the Cartan matrix of $`A`, then $`\det(C) = \pm 1`.

(ii) What is the homological dimension of $`k[t]/t^n`, $`n > 1`? Of the algebra of Problem 9.3.2?

## Formalization
%%%
tag := "Chapter9/Problem9.4.5/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.LinearAlgebra.Module.Projective.designatedRing_value_eq_top}

{Manual.docstring RepresentationTheory.LinearAlgebra.Module.Projective.quotientPolynomialXPower_value_eq_top}

### Supporting declarations

{Manual.docstring RepresentationTheory.LinearAlgebra.Module.Projective.unrenderedMatrixTheorem}
