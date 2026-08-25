/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter4.Problem414

#doc (Manual) "Irreducible representations of p-groups in characteristic p are trivial" =>

# Irreducible representations of p-groups in characteristic p are trivial
%%%
tag := "Chapter4/Problem4.1.4"
number := false
%%%
**Problem 4.1.4.** Let $`G` be a group of order $`p^n`. Show that every irreducible representation of $`G` over a field $`k` of characteristic $`p` is trivial.

## Formalization
%%%
tag := "Chapter4/Problem4.1.4/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.ModularPGroup.eq_id_of_isSimpleModule_of_card_eq_primePow}
