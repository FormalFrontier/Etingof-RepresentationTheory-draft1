/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter7.Exercise798

#doc (Manual) "Reflection functors as adjoint pair" =>

# Reflection functors as adjoint pair
%%%
tag := "Chapter7/Exercise7.9.8"
number := false
%%%

*Exercise 7.9.8.* (a) Let $`Q` be a quiver and let $`i \in Q` be a source. Let $`V` be a representation of $`Q` and let $`W` be a representation of $`\overline{Q}_i` (the quiver obtained from $`Q` by reversing arrows at the vertex $`i`). Prove that there is a natural isomorphism between $`\operatorname{Hom}(F_i^- V, W)` and $`\operatorname{Hom}(V, F_i^+ W)`. In other words, the functor $`F_i^+` is right adjoint to $`F_i^-`.

(b) Deduce that the functor $`F_i^+` is left exact and $`F_i^-` is right exact.

## Formalization
%%%
tag := "Chapter7/Exercise7.9.8/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Quiver.EndofunctorAdjunction.adjunction}

{Manual.docstring RepresentationTheory.Quiver.EndofunctorAdjunction.auxiliaryEndofunctorConditions}

### Supporting declarations

{Manual.docstring RepresentationTheory.Quiver.EndofunctorAdjunction.auxiliaryLeftEndofunctorCondition}

{Manual.docstring RepresentationTheory.Quiver.EndofunctorAdjunction.auxiliaryRightEndofunctorCondition}
