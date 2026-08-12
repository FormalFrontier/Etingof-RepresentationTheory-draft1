/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Lemma526

#doc (Manual) "Algebraic conjugates of sums are sums of algebraic conjugates" =>

# Algebraic conjugates of sums are sums of algebraic conjugates
%%%
tag := "Chapter5/Lemma5.2.6"
number := false
%%%

**Lemma 5.2.6.** _If $`\alpha_1, \ldots, \alpha_m` are algebraic numbers, then all algebraic conjugates to $`\alpha_1 + \cdots + \alpha_m` are of the form $`\alpha_1' + \cdots + \alpha_m'`, where $`\alpha_i'` are some algebraic conjugates of $`\alpha_i`._
**Proof.** It suffices to prove this for two summands. If $`\alpha_i` are eigenvalues of rational matrices $`A_i` of smallest size (i.e., their characteristic polynomials are the minimal polynomials of $`\alpha_i`), then $`\alpha_1 + \alpha_2` is an eigenvalue of $`A := A_1 \otimes \mathrm{Id} + \mathrm{Id} \otimes A_2`. Therefore, so is any algebraic conjugate to $`\alpha_1 + \alpha_2`. But all eigenvalues of $`A` are of the form $`\alpha_1' + \alpha_2'`, so we are done. $`\square`

## Formalization
%%%
tag := "Chapter5/Lemma5.2.6/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Algebraic.ConjRoot.FiniteSum.exists_conjRoots_sum_eq_of_isConjRoot_sum}
