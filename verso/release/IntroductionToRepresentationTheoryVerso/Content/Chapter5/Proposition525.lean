/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Proposition525

#doc (Manual) "Algebraic integers intersect rationals in the integers" =>

# Algebraic integers intersect rationals in the integers
%%%
tag := "Chapter5/Proposition5.2.5"
number := false
%%%
**Proposition 5.2.5.** $`\overline{\mathbb{Z}} \cap \mathbb{Q} = \mathbb{Z}`.

**Proof.** We will be using Definition 5.2.1. Let $`z` be a root of

$$`p(x) = x^n + a_1 x^{n-1} + \ldots + a_{n-1} x + a_n,`

and suppose

$$`z = \frac{p}{q} \in \mathbb{Q}, \quad \gcd(p, q) = 1.`

Notice that the leading term of $`p(z)` will have $`q^n` in the denominator, whereas all the other terms will have a lower power of $`q` there. Thus, if $`q \neq \pm 1`, then $`p(z) \notin \mathbb{Z}`, a contradiction. Thus, $`z \in \overline{\mathbb{Z}} \cap \mathbb{Q} \Rightarrow z \in \mathbb{Z}`. The reverse inclusion follows because $`n \in \mathbb{Z}` is a root of $`x - n`. $`\square`

## Formalization
%%%
tag := "Chapter5/Proposition5.2.5/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.NumberTheory.IntegralClosure.Rat.Rat.isIntegral_complex_iff}
