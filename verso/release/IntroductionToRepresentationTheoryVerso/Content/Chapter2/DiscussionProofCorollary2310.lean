/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso Genre

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.DiscussionProofCorollary2310

#doc (Manual) "Proof of Corollary 2.3.10" =>
# Proof of Corollary 2.3.10
%%%
tag := "Chapter2/Discussion_proof_Corollary2.3.10"
number := false
%%%
*Proof.* Let $`\lambda` be an eigenvalue of $`\phi` (a root of the characteristic polynomial of $`\phi`). It exists since $`k` is an algebraically closed field. Then the operator $`\phi - \lambda \operatorname{Id}` is an intertwining operator $`V \to V`, which is not an isomorphism (since its determinant is zero). Thus by Proposition 2.3.9 this operator is zero, hence the result. $`\square`

## Formalization
%%%
tag := "Chapter2/Discussion_proof_Corollary2.3.10/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.SimpleModule.Endomorphisms.endomorphism_eq_smul}
