/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.Theorem381

#doc (Manual) "The Krull-Schmidt theorem" =>

# The Krull-Schmidt theorem
%%%
tag := "Chapter3/Theorem3.8.1"
number := false
%%%
**Theorem 3.8.1** (Krull-Schmidt theorem). _Any finite dimensional representation of $`A` can be uniquely (up to an isomorphism and the order of summands) decomposed into a direct sum of indecomposable representations._

**Proof.** It is clear that a decomposition of $`V` into a direct sum of indecomposable representations exists, so we just need to prove uniqueness. We will prove it by induction on $`\dim V`. Let $`V = V_1 \oplus \cdots \oplus V_m = V'_1 \oplus \cdots \oplus V'_n`. Let $`i_s : V_s \to V`, $`i'_s : V'_s \to V`, $`p_s : V \to V_s`, $`p'_s : V \to V'_s` be the natural maps associated with these decompositions. Let $`\theta_s = p_1 i'_s p'_s i_1 : V_1 \to V_1`. We have $`\sum_{s=1}^n \theta_s = 1`. Now we need the following lemma.

## Formalization
%%%
tag := "Chapter3/Theorem3.8.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Module.IndependentSpanningFamilies.eq_card_and_exists_equiv_of_iSupIndep}

{Manual.docstring RepresentationTheory.Algebra.Module.IndependentSpanningFamilies.exists_iSupIndep_eq_top}
