/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Definition2142

#doc (Manual) "Dual representation of a Lie algebra" =>
# Dual representation of a Lie algebra
%%%
tag := "Chapter2/Definition2.14.2"
number := false
%%%
**Definition 2.14.2.** The **dual representation** $`V^*` to a representation $`V` of a Lie algebra $`\mathfrak{g}` is the dual space $`V^*` to $`V` with $`\rho_{V^*}(x) = -\rho_V(x)^*`.

It is easy to check that these are indeed representations.

## Formalization
%%%
tag := "Chapter2/Definition2.14.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Lie.AuxiliarySingleModuleType.auxiliary_lie_bracket_apply}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.Lie.AuxiliarySingleModuleType.AuxiliaryLieModuleType}
