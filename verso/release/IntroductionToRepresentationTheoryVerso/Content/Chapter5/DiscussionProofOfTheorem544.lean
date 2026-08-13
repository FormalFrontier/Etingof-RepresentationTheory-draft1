/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.DiscussionProofOfTheorem544

#doc (Manual) "Proof of Theorem 5.4.4" =>

# Proof of Theorem 5.4.4
%%%
tag := "Chapter5/Discussion_proof_of_Theorem5.4.4"
number := false
%%%

**Proof of Theorem 5.4.4.** Let $`\dim V = n`. Let $`\varepsilon_1, \varepsilon_2, \ldots, \varepsilon_n` be the eigenvalues of $`\rho_V(g)`. They are roots of unity, so $`\chi_V(g)` is an algebraic integer. Also, by Proposition 5.3.2, $`\frac{1}{n}|C|\chi_V(g)` is an algebraic integer. Since $`\gcd(n, |C|) = 1`, there exist integers $`a, b` such that $`a|C| + bn = 1`. This implies that

$$`\frac{a|C|\chi_V(g)}{n} + b\chi_V(g) = \frac{\chi_V(g)}{n} = \frac{1}{n}(\varepsilon_1 + \cdots + \varepsilon_n)`

is an algebraic integer. Thus, by Lemma 5.4.5, we get that either $`\varepsilon_1 = \cdots = \varepsilon_n` or $`\varepsilon_1 + \cdots + \varepsilon_n = \chi_V(g) = 0`. In the first case, since $`\rho_V(g)` is diagonalizable, it must be scalar. In the second case, $`\chi_V(g) = 0`. The theorem is proved. $`\square`

## Formalization
%%%
tag := "Chapter5/Discussion_proof_of_Theorem5.4.4/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.Complex.RootsOfUnity.AverageIntegral.rootsOfUnity_all_eq_or_sum_eq_zero_of_average_integral}

{Manual.docstring RepresentationTheory.FiniteGroupCharacterCoprimality.character_eq_zero_or_action_eq_smul_id_of_conjClassCard_coprime_finrank}
