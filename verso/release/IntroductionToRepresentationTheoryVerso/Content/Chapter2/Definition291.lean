/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Definition291

#doc (Manual) "Lie algebra" =>
# Lie algebra
%%%
tag := "Chapter2/Definition2.9.1"
number := false
%%%
**Definition 2.9.1.** $`(\mathfrak{g}, [\ ,\ ])` is a **Lie algebra** if $`[\ ,\ ]` satisfies the Jacobi identity

$$`(2.9.1) \qquad [[a, b], c] + [[b, c], a] + [[c, a], b] = 0.`

## Formalization
%%%
tag := "Chapter2/Definition2.9.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Lie.Basic.LieRing.cyclic_iterated_bracket_sum_eq_zero}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.Lie.Basic.LieRing.AuxiliaryType}
