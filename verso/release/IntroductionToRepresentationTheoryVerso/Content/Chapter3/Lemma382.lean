/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.Lemma382

#doc (Manual) "Endomorphisms of indecomposable representations are isomorphisms or nilpotent" =>
# Endomorphisms of indecomposable representations are isomorphisms or nilpotent
%%%
tag := "Chapter3/Lemma3.8.2"
number := false
%%%
**Lemma 3.8.2.** _Let $`W` be a finite dimensional indecomposable representation of $`A`. Then:_

_(i) Any homomorphism $`\theta : W \to W` is either an isomorphism or nilpotent._

_(ii) If $`\theta_s : W \to W`, $`s = 1, \ldots, n`, are nilpotent homomorphisms, then so is $`\theta := \theta_1 + \cdots + \theta_n`._
**Proof.** (i) Generalized eigenspaces of $`\theta` are subrepresentations of $`W`, and $`W` is their direct sum. Thus, $`\theta` can have only one eigenvalue $`\lambda`. If $`\lambda` is zero, $`\theta` is nilpotent; otherwise it is an isomorphism.

(ii) The proof is by induction in $`n`. The base is clear. To make the induction step ($`n - 1` to $`n`), assume that $`\theta` is not nilpotent. Then by (i), $`\theta` is an isomorphism, so $`\sum_{i=1}^n \theta^{-1} \theta_i = 1`. The morphisms $`\theta^{-1} \theta_i` are not isomorphisms, so they are nilpotent. Thus $`1 - \theta^{-1} \theta_n = \theta^{-1} \theta_1 + \cdots + \theta^{-1} \theta_{n-1}` is an isomorphism, which is a contradiction to the induction assumption. $`\square`

By the lemma, we find that for some $`s`, $`\theta_s` must be an isomorphism; we may assume that $`s = 1`. In this case, $`V'_1 = \operatorname{Im}(p'_1 i_1) \oplus \ker(p_1 i'_1)`, so since $`V'_1` is indecomposable, we get that $`f := p'_1 i_1 : V_1 \to V'_1` and $`g := p_1 i'_1 : V'_1 \to V_1` are isomorphisms.

## Formalization
%%%
tag := "Chapter3/Lemma3.8.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Module.EndomorphismDichotomy.bijective_or_nilpotent_of_auxiliaryProperty}

{Manual.docstring RepresentationTheory.Algebra.Module.EndomorphismDichotomy.sum_nilpotent_of_auxiliaryProperty}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.Module.IndependentSpanningFamilies.eq_card_and_exists_equiv_of_iSupIndep}
