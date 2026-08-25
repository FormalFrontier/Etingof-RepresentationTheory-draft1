/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.DiscussionProofOfTheorem5261

#doc (Manual) "Proof of Artin's theorem (both directions)" =>

# Proof of Artin's theorem (both directions)
%%%
tag := "Chapter5/Discussion_proof_of_Theorem5.26.1"
number := false
%%%

*Proof.* _Proof that (ii) implies (i)._ Assume that $`g \in G` does not belong to any of the subgroups $`H \in X`. Then, since $`X` is conjugation invariant, it cannot be conjugated into such a subgroup. Hence by the Frobenius formula, $`\chi_{\operatorname{Ind}_H^G(V)}(g) = 0` for all $`H \in X` and $`V`. So by (ii), for any irreducible representation $`W` of $`G`, $`\chi_W(g) = 0`. But irreducible characters span the space of class functions, so any class function vanishes on $`g`, which is a contradiction.

_Proof that (i) implies (ii)._ Let $`U` be a virtual representation of $`G` over $`\mathbb{C}` (i.e., a linear combination of irreducible representations with nonzero integer coefficients) such that $`(\chi_U, \chi_{\operatorname{Ind}_H^G V}) = 0` for all $`H, V`. So by Frobenius reciprocity, $`(\chi_{U|_H}, \chi_V) = 0`. This means that $`\chi_U` vanishes on $`H` for any $`H \in X`. Hence by (i), $`\chi_U` is identically zero. This implies (ii) (because of Remark 5.26.2). $`\square`

## Formalization
%%%
tag := "Chapter5/Discussion_proof_of_Theorem5.26.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.AuxiliarySubgroupFunctions.auxiliary_cover_iff_character_mem_span}
