/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter6.Definition6410

#doc (Manual) "Definition 6.4.10: Reflection and simple reflections" =>

# Definition 6.4.10: Reflection and simple reflections
%%%
tag := "Chapter6/Definition6.4.10"
number := false
%%%

*Definition 6.4.10.* Let $`\alpha \in \mathbb{Z}^n` be a positive root. The reflection $`s_\alpha` is defined by the formula

$$`s_\alpha(v) = v - B(v, \alpha)\alpha.`

We denote $`s_{\alpha_i}` by $`s_i` and call these *simple reflections*.

## Formalization
%%%
tag := "Chapter6/Definition6.4.10/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryCoordinateTransform}

{Manual.docstring RepresentationTheory.AuxiliaryIntegerVectorTransforms.auxiliaryVectorTransform}
