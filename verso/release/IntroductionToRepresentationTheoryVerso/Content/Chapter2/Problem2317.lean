/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Problem2317

#doc (Manual) "End\\_A(A) = A^op" =>
# End\_A(A) = A^op
%%%
tag := "Chapter2/Problem2.3.17"
number := false
%%%
**Problem 2.3.17.** Let $`A` be an associative algebra, and let $`V` be a representation of $`A`. By $`\operatorname{End}_A(V)` one denotes the algebra of all homomorphisms of representations $`V \to V`. Show that $`\operatorname{End}_A(A) = A^{\mathrm{op}}`, the algebra $`A` with opposite multiplication.

## Formalization
%%%
tag := "Chapter2/Problem2.3.17/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.ModuleEnd.OppositeRing.regularEndRingEquivOpposite}

### Supporting declarations

{Manual.docstring RepresentationTheory.ModuleEnd.OppositeRing.regularEndRingEquivOpposite_apply}

{Manual.docstring RepresentationTheory.ModuleEnd.OppositeRing.regularEndRingEquivOpposite_symm_apply}
