/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Lemma572

#doc (Manual) "Virtual representation with inner product 1 and positive dimension is irreducible" =>

# Virtual representation with inner product 1 and positive dimension is irreducible
%%%
tag := "Chapter5/Lemma5.7.2"
number := false
%%%

**Lemma 5.7.2.** _Let $`V` be a virtual representation with character $`\chi_V`. If $`(\chi_V, \chi_V) = 1` and $`\chi_V(1) > 0`, then $`\chi_V` is a character of an irreducible representation of $`G`._

**Proof.** Let $`V_1, V_2, \ldots, V_m` be the irreducible representations of $`G`, and let $`V = \sum n_i V_i`. Then by orthonormality of characters, $`(\chi_V, \chi_V) = \sum_i n_i^2`. So $`\sum_i n_i^2 = 1`, meaning that $`n_i = \pm 1` for exactly one $`i` and $`n_j = 0` for $`j \neq i`. But $`\chi_V(1) > 0`, so $`n_i = +1` and we are done. $`\square`

## Formalization
%%%
tag := "Chapter5/Lemma5.7.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.FiniteGroup.Character.Irreducibility.exists_singleton_of_character_selfInner_eq_one}
