/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Theorem544

#doc (Manual) "Character vanishes or element acts as scalar when gcd(|C|, dim V) = 1" =>

# Character vanishes or element acts as scalar when gcd(|C|, dim V) = 1
%%%
tag := "Chapter5/Theorem5.4.4"
number := false
%%%

**Theorem 5.4.4.** _Let $`V` be an irreducible representation of a finite group $`G` and let $`C` be a conjugacy class of $`G` with $`\gcd(|C|, \dim(V)) = 1`. Then for any $`g \in C`, either $`\chi_V(g) = 0` or $`g` acts as a scalar on $`V`._

## Formalization
%%%
tag := "Chapter5/Theorem5.4.4/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.FiniteGroupCharacterCoprimality.character_eq_zero_or_action_eq_smul_id_of_conjClassCard_coprime_finrank}
