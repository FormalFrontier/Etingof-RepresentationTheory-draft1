/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter4.Theorem463

#doc (Manual) "Unitary representations are completely reducible" =>

# Unitary representations are completely reducible
%%%
tag := "Chapter4/Theorem4.6.3"
number := false
%%%

**Theorem 4.6.3.** _A finite dimensional unitary representation $`V` of any group $`G` is completely reducible._

**Proof.** Let $`W` be a subrepresentation of $`V`. Let $`W^\perp` be the orthogonal complement of $`W` in $`V` under the Hermitian inner product. Then $`W^\perp` is a subrepresentation of $`V`, and $`V = W \oplus W^\perp`. This implies that $`V` is completely reducible. $`\square`

## Formalization
%%%
tag := "Chapter4/Theorem4.6.3/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.InvariantComplements.exists_invariant_isCompl_of_preserves_inner}
