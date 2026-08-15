/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Theorem543

#doc (Manual) "Burnside's theorem: groups of order p^a q^b are solvable" =>

# Burnside's theorem: groups of order p^a q^b are solvable
%%%
tag := "Chapter5/Theorem5.4.3"
number := false
%%%

**Theorem 5.4.3** (Burnside). _Any group $`G` of order $`p^a q^b`, where $`p` and $`q` are primes and $`a, b \geq 0`, is solvable._

## Formalization
%%%
tag := "Chapter5/Theorem5.4.3/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.FiniteGroupSolvability.isSolvable_of_card_eq_prime_pow_mul_prime_pow}
