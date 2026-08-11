/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter4.DiscussionAfterTheorem451

#doc (Manual) "Irreducibility criterion via character inner product" =>

# Irreducibility criterion via character inner product
%%%
tag := "Chapter4/Discussion_after_Theorem4.5.1"
number := false
%%%

Theorem 4.5.1 gives a powerful method of checking if a given complex representation $`V` of a finite group $`G` is irreducible. Indeed, it implies that $`V` is irreducible if and only if $`(\chi_V, \chi_V) = 1`.

## Formalization
%%%
tag := "Chapter4/Discussion_after_Theorem4.5.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Group.SimpleCharacterCriterion.simple_iff_characterInner_eq_one}
