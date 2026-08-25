/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Lemma547

#doc (Manual) "Existence of V in N with nonzero character value" =>

# Existence of V in N with nonzero character value
%%%
tag := "Chapter5/Lemma5.4.7"
number := false
%%%

**Lemma 5.4.7.** _There exists $`V \in N` such that $`\chi_V(g) \neq 0`._
**Proof.** If $`V \in D`, the number $`\frac{1}{p}\dim(V)\chi_V(g)` is an algebraic integer, so

$$`a = \sum_{V \in D} \frac{1}{p} \dim(V) \chi_V(g)`

is an algebraic integer.

Now, by (5.4.1), we have

$$`0 = \chi_C(g) + \sum_{V \in D} \dim V \chi_V(g) + \sum_{V \in N} \dim V \chi_V(g)`

$$`= 1 + pa + \sum_{V \in N} \dim V \chi_V(g).`

This means that the last summand is nonzero. $`\square`

## Formalization
%%%
tag := "Chapter5/Lemma5.4.7/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.FiniteGroup.PrimePowerConjugacyClass.exists_simple_representation_of_conj_class_card_prime_pow}
