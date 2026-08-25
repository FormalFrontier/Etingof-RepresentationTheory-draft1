/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.DiscussionFootnote515

#doc (Manual) "Footnote on lexicographic ordering of sigma(rho)" =>

# Footnote on lexicographic ordering of sigma(rho)
%%%
tag := "Chapter5/Discussion_footnote_5.15"
number := false
%%%

---

$`{}^2`Another way to see this is to note that $`\sigma(\rho) \leq \rho` lexicographically with equality if and only if $`\sigma = 1`, and subtracting both sides from the constant vector $`\lambda + \rho` shows that $`\lambda + \rho - \sigma(\rho) \geq \lambda` with equality if and only if $`\sigma = 1`.

## Formalization
%%%
tag := "Chapter5/Discussion_footnote_5.15/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.LexicographicPermutations.auxiliaryIndexValue_comp_perm_eq_iff}

{Manual.docstring RepresentationTheory.LexicographicPermutations.auxiliaryIndexValue_comp_perm_le}

{Manual.docstring RepresentationTheory.LexicographicPermutations.partitionAuxiliaryValue_eq_adjusted_perm_iff}

{Manual.docstring RepresentationTheory.LexicographicPermutations.partitionAuxiliaryValue_le_adjusted_perm}
