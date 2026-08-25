/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter4.Introduction45

#doc (Manual) "Section 4.5: Orthogonality of characters \u2014 Hermitian inner product on class functions" =>

# Section 4.5: Orthogonality of characters — Hermitian inner product on class functions
%%%
tag := "Chapter4/Introduction_4.5"
number := false
%%%

## 4.5. Orthogonality of characters
%%%
tag := "Chapter4/Introduction_4.5/heading-1"
%%%

We define a positive definite Hermitian inner product on $`\mathrm{F}_c(G, \mathbb{C})` (the space of central functions) by

$$`(f_1, f_2) = \frac{1}{|G|} \sum_{g \in G} f_1(g)\overline{f_2(g)}.`
The following theorem says that characters of irreducible representations of $`G` form an orthonormal basis of $`F_c(G, \mathbb{C})` under this inner product.

## Formalization
%%%
tag := "Chapter4/Introduction_4.5/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.FiniteGroup.CharacterPairing.FiniteGroup.normalized_characterPairing_eq_finrank_hom}

{Manual.docstring RepresentationTheory.FiniteGroup.CharacterPairing.FiniteGroup.normalized_characterPairing_of_simple}

{Manual.docstring RepresentationTheory.FiniteGroup.ClassFunctions.FiniteGroup.span_simple_characters_eq_auxiliarySubmodule}
