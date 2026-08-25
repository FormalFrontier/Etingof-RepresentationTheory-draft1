/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.DiscussionProofOfProposition5141

#doc (Manual) "Proof of Proposition 5.14.1" =>

# Proof of Proposition 5.14.1
%%%
tag := "Chapter5/Discussion_proof_of_Proposition5.14.1"
number := false
%%%

*Proof.* By Lemmas 5.13.3 and 5.13.4,

$$`\operatorname{Hom}(U_\lambda, V_\mu) = \operatorname{Hom}(\mathbb{C}[S_n]a_\lambda, \mathbb{C}[S_n]a_\mu b_\mu) = a_\lambda \mathbb{C}[S_n] a_\mu b_\mu,`

and the result follows from Lemmas 5.13.1 and 5.13.2. $`\square`

## Formalization
%%%
tag := "Chapter5/Discussion_proof_of_Proposition5.14.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.AuxiliaryPartitionLinearEquivalences.auxiliaryDirectSumLinearEquiv}

{Manual.docstring RepresentationTheory.PartitionLinearMapVanishing.finrank_linearMap_to_mem_eq_one}

{Manual.docstring RepresentationTheory.PartitionLinearMapVanishing.linearMap_to_mem_eq_zero_of_not_partitionRelation}
