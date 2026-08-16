/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter4.Exercise431

#doc (Manual) "2-dimensional irreducible representation of Q\\_8 via functions" =>

# 2-dimensional irreducible representation of Q\_8 via functions
%%%
tag := "Chapter4/Exercise4.3.1"
number := false
%%%

**Exercise 4.3.1.** Show that the 2-dimensional irreducible representation of $`Q_8` can be realized in the space of functions $`f : Q_8 \to \mathbb{C}` such that $`f(gi) = \sqrt{-1}f(g)` (the action of $`G` is by right multiplication, $`g \circ f(x) = f(xg)`).

## Formalization
%%%
tag := "Chapter4/Exercise4.3.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.QuaternionFunctionSubmodule.auxiliaryFunctionSubmodule_invariant}

{Manual.docstring RepresentationTheory.QuaternionFunctionSubmodule.finrank_auxiliaryFunctionSubmodule}

{Manual.docstring RepresentationTheory.QuaternionFunctionSubmodule.invariant_submodule_eq_bot_or_auxiliaryFunctionSubmodule}
