/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter4.Example413

#doc (Manual) "Irreducible representations of Z/pZ in characteristic p are trivial" =>

# Irreducible representations of Z/pZ in characteristic p are trivial
%%%
tag := "Chapter4/Example4.1.3"
number := false
%%%
**Example 4.1.3.** If $`G = \mathbb{Z}/p\mathbb{Z}` and $`k` has characteristic $`p`, then every irreducible representation of $`G` over $`k` is trivial (so $`k[\mathbb{Z}/p\mathbb{Z}]` indeed is not semisimple). Indeed, an irreducible representation of this group is a 1-dimensional space on which the generator acts by a $`p`th root of unity. But every $`p`th root of unity in $`k` equals 1, as $`x^p - 1 = (x - 1)^p` over $`k`.

## Formalization
%%%
tag := "Chapter4/Example4.1.3/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Group.CyclicPrimeRepresentation.apply_eq_id_of_isSimpleModule}

### Supporting declarations

{Manual.docstring RepresentationTheory.SemisimpleGroupAlgebraCardinality.isUnit_card_of_isSemisimpleRing}
