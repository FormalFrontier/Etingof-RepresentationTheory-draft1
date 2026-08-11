/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.DiscussionAfterProposition525

#doc (Manual) "Minimal polynomial, algebraic conjugates, and Vieta's theorem" =>

# Minimal polynomial, algebraic conjugates, and Vieta's theorem
%%%
tag := "Chapter5/Discussion_after_Proposition5.2.5"
number := false
%%%
Every algebraic number $`\alpha` has a **minimal polynomial** $`p(x)` which is the monic polynomial with rational coefficients of the smallest degree such that $`p(\alpha) = 0`. Any other polynomial $`q(x)` with rational coefficients such that $`q(\alpha) = 0` is divisible by $`p(x)`. Roots of $`p(x)` are called the **algebraic conjugates** of $`\alpha`; they are roots of any polynomial $`q` with rational coefficients such that $`q(\alpha) = 0`.

Note that any algebraic conjugate of an algebraic integer is obviously also an algebraic integer. Therefore, by the Vieta theorem, the minimal polynomial of an algebraic integer has integer coefficients.

Below we will need the following lemma:
