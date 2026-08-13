/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter6.Definition651

#doc (Manual) "Definition 6.5.1: Dimension vector" =>

# Definition 6.5.1: Dimension vector
%%%
tag := "Chapter6/Definition6.5.1"
number := false
%%%

*Definition 6.5.1.* Let $`Q` be a quiver with any labeling $`1, \ldots, n` of the vertices. Let $`V = (V_1, \ldots, V_n)` be a representation of $`Q`. We then call

$$`d(V) = (\dim V_1, \ldots, \dim V_n)`

*the dimension vector* of this representation.

## Formalization
%%%
tag := "Chapter6/Definition6.5.1/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.AuxiliaryFiniteDimensionalFamily.auxiliaryNatValue}
