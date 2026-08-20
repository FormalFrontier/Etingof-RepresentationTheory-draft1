/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.DiscussionProofOfTheorem381

#doc (Manual) "Completion of proof of the Krull-Schmidt theorem" =>

# Completion of proof of the Krull-Schmidt theorem
%%%
tag := "Chapter3/Discussion_proof_of_Theorem3.8.1"
number := false
%%%
Let $`B = \bigoplus_{j>1} V_j`, $`B' = \bigoplus_{j>1} V'_j`; then we have $`V = V_1 \oplus B = V'_1 \oplus B'`. Consider the map $`h : B \to B'` defined as a composition of the natural maps $`B \to V \to B'` attached to these decompositions. We claim that $`h` is an isomorphism. To show this, it suffices to show that $`\ker h = 0` (as $`h` is a map between spaces of the same dimension). Assume that $`v \in \ker h \subset B`. Then $`v \in V'_1`. On the other hand, the projection of $`v` to $`V_1` is zero, so $`gv = 0`. Since $`g` is an isomorphism, we get $`v = 0`, as desired.

Now by the induction assumption, $`m = n`, and $`V_j \cong V'_{\sigma(j)}` for some permutation $`\sigma` of $`2, \ldots, n`. The theorem is proved. $`\square`

## Formalization
%%%
tag := "Chapter3/Discussion_proof_of_Theorem3.8.1/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.Module.IndependentSpanningFamilies.eq_card_and_exists_equiv_of_iSupIndep}
