/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.DiscussionProofOfTheorem543

#doc (Manual) "Proof of Burnside's theorem" =>

# Proof of Burnside's theorem
%%%
tag := "Chapter5/Discussion_proof_of_Theorem5.4.3"
number := false
%%%

**Proof of Burnside's theorem.** Assume Burnside's theorem is false. Then there exists a nonsolvable group $`G` of order $`p^a q^b`. Let $`G` be the smallest such group. Then $`G` is simple, and by Theorem 5.4.6, it cannot have a conjugacy class of order $`p^k` or $`q^k`, $`k \geq 1`. So the order of any conjugacy class in $`G` either equals 1 or is divisible by $`pq`. Adding the orders of conjugacy classes and equating the sum to $`p^a q^b`, we see that there has to be more than one conjugacy class consisting just of one element. So $`G` has a nontrivial center, which gives a contradiction. $`\square`

## Formalization
%%%
tag := "Chapter5/Discussion_proof_of_Theorem5.4.3/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.FiniteGroupNormalSubgroups.exists_nontrivial_proper_normalSubgroup_of_conjClassCard_eq_prime_pow}

{Manual.docstring RepresentationTheory.FiniteGroupSolvability.isSolvable_of_card_eq_prime_pow_mul_prime_pow}
