/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Theorem531

#doc (Manual) "Dimension of irreducible representation divides order of group" =>

# Dimension of irreducible representation divides order of group
%%%
tag := "Chapter5/Theorem5.3.1"
number := false
%%%

**Theorem 5.3.1.** _Let $`G` be a finite group, and let $`V` be an irreducible representation of $`G` over $`\mathbb{C}`. Then_

$$`\dim V \text{ divides } |G|.`
**Proof.** Let $`C_1, C_2, \ldots, C_n` be the conjugacy classes of $`G`. Let $`g_{C_i}` be representatives of $`C_i`. Set

$$`\lambda_i = \chi_V(g_{C_i}) \frac{|C_i|}{\dim V}.`

## Formalization
%%%
tag := "Chapter5/Theorem5.3.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.FiniteGroupCharacterArithmetic.finrank_dvd_card_of_simple}

### Supporting declarations

{Manual.docstring RepresentationTheory.CharacterIntegrality.isIntegral_card_conjClass_mul_character_div_finrank}
