/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.DiscussionEndOfLemma5131Proof

#doc (Manual) "End of proof of Lemma 5.13.1 (statement on missing page)" =>

# End of proof of Lemma 5.13.1 (statement on missing page)
%%%
tag := "Chapter5/Discussion_end_of_Lemma5.13.1_proof"
number := false
%%%

Any two elements in the first row of $`T` must be in different columns of $`T'`, so there exists $`q'_1 \in Q'_\lambda` which moves all these elements to the first row. So there is $`p_1 \in P_\lambda` such that $`p_1 T` and $`q'_1 T'` have the same first row. Now do the same procedure with the second row, finding elements $`p_2, q'_2` such that $`p_2 p_1 T` and $`q'_2 q'_1 T'` have the same first two rows. Continuing so, we will construct the desired elements $`p, q'`. The lemma is proved. $`\square`

## Formalization
%%%
tag := "Chapter5/Discussion_end_of_Lemma5.13.1_proof/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra.exists_swap_mem_left_of_not_mem_mul}
