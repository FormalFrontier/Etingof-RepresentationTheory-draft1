/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Lemma5132

#doc (Manual) "a\\_lambda C\\[S\\_n\\] b\\_mu = 0 when lambda > mu lexicographically" =>

# a\_lambda C\[S\_n\] b\_mu = 0 when lambda > mu lexicographically
%%%
tag := "Chapter5/Lemma5.13.2"
number := false
%%%

*Lemma 5.13.2.* _If $`\lambda > \mu`, then $`a_\lambda \mathbb{C}[S_n] b_\mu = 0`._

*Proof.* Similarly to the previous lemma, it suffices to show that for any $`g \in S_n` there exists a transposition $`t \in P_\lambda` such that $`g^{-1}tg \in Q_\mu`. Let $`T = T_\lambda` and $`T' = gT_\mu`. We claim that there are two integers which are in the same row of $`T` and the same column of $`T'`. Indeed, if $`\lambda_1 > \mu_1`, this is clear by the pigeonhole principle (already for the first row). Otherwise, if $`\lambda_1 = \mu_1`, as in the proof of the previous lemma, we can find elements $`p_1 \in P_\lambda`, $`q'_1 \in gQ_\mu g^{-1}` such that $`p_1 T` and $`q'_1 T'` have the same first row and repeat the argument for the second row, and so on. Eventually, having done $`i-1` such steps, we'll have $`\lambda_i > \mu_i`, which means that some two elements of the $`i`th row of the first tableau are in the same column of the second tableau, completing the proof. $`\square`

## Formalization
%%%
tag := "Chapter5/Lemma5.13.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.SymmetricGroup.PartitionDominance.sandwich_eq_zero_of_lexLt}

### Supporting declarations

{Manual.docstring RepresentationTheory.SymmetricGroup.PartitionDominance.Partition.LexLt.not_dominates}

{Manual.docstring RepresentationTheory.SymmetricGroup.PartitionDominance.auxiliaryUnavailableStatement022059}

{Manual.docstring RepresentationTheory.SymmetricGroup.PartitionDominance.sandwich_eq_zero_of_not_dominates}

{Manual.docstring RepresentationTheory.SymmetricGroup.PartitionDominance.sandwich_eq_zero_of_strictDominates}

{Manual.docstring RepresentationTheory.SymmetricGroup.PartitionDominance.sandwich_single_eq_zero_of_not_dominates}
