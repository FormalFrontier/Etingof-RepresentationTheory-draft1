/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Theorem5171

#doc (Manual) "Hook length formula: dim V\\_lambda = n! / product of hook lengths" =>

# Hook length formula: dim V\_lambda = n! / product of hook lengths
%%%
tag := "Chapter5/Theorem5.17.1"
number := false
%%%

*Theorem 5.17.1* (The hook length formula). _One has_

$$`\dim V_\lambda = \frac{n!}{\prod_{(i,j): i \leq \lambda_j} h(i, j)}.`

*Proof.* The formula follows from formula (5.17.1). Namely, note that

$$`\frac{l_1!}{\prod_{1 < j \leq N} (l_1 - l_j)} = \prod_{1 \leq k \leq l_1, k \neq l_1 - l_j} k.`

It is easy to see that the factors in this product are exactly the hook lengths $`h(i, 1)`. Now delete the first row of the diagram and proceed by induction. $`\square`
