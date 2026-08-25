/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso Genre

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Definition226

#doc (Manual) "Homomorphism of algebras" =>
# Homomorphism of algebras
%%%
tag := "Chapter2/Definition2.2.6"
number := false
%%%
*Definition 2.2.6.* A *homomorphism of algebras* $`f : A \to B` is a linear map such that $`f(xy) = f(x)f(y)` for all $`x, y \in A` and $`f(1) = 1`.

## Formalization
%%%
tag := "Chapter2/Definition2.2.6/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.AuxiliaryAlgebraPairType.AuxiliaryAlgebraPairType}
