/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.DiscussionProofCorollary2312

#doc (Manual) "Proof of Corollary 2.3.12" =>
# Proof of Corollary 2.3.12
%%%
tag := "Chapter2/Discussion_proof_Corollary2.3.12"
number := false
%%%
**Proof.** Let $`V` be irreducible. For any element $`a \in A`, the operator $`\rho(a) : V \to V` is an intertwining operator. Indeed,

$$`\rho(a)\rho(b)v = \rho(ab)v = \rho(ba)v = \rho(b)\rho(a)v`

(the second equality is true since the algebra is commutative). Thus, by Schur's lemma, $`\rho(a)` is a scalar operator for any $`a \in A`. Hence every subspace of $`V` is a subrepresentation. But $`V` is irreducible, so $`0` and $`V` are the only subspaces of $`V`. This means that $`\dim V = 1` (since $`V \neq 0`). $`\square`

## Formalization
%%%
tag := "Chapter2/Discussion_proof_Corollary2.3.12/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.SimpleModule.Dimension.finrank_eq_one}

{Manual.docstring RepresentationTheory.Algebra.SimpleModule.Endomorphisms.endomorphism_eq_smul}
