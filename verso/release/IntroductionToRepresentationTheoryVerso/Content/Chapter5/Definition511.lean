/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Definition511

#doc (Manual) "Complex, real, and quaternionic type of irreducible representations" =>

# Complex, real, and quaternionic type of irreducible representations
%%%
tag := "Chapter5/Definition5.1.1"
number := false
%%%
**Definition 5.1.1.** We say that $`V` is

- of **complex type** if $`V \not\cong V^*`,
- of **real type** if $`V` has a nondegenerate symmetric form invariant under $`G`,
- of **quaternionic type** if $`V` has a nondegenerate skew form invariant under $`G`.

## Formalization
%%%
tag := "Chapter5/Definition5.1.1/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionOne}

{Manual.docstring RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationConditionTwo}

{Manual.docstring RepresentationTheory.FiniteGroupRepresentations.Auxiliary.auxiliaryRepresentationProperty}
