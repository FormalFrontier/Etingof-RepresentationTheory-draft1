/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter4.Problem41210

#doc (Manual) "Faithful representations contain all irreducibles in symmetric powers" =>

# Faithful representations contain all irreducibles in symmetric powers
%%%
tag := "Chapter4/Problem4.12.10"
number := false
%%%

**Problem 4.12.10.** Let $`G` be a finite group and let $`V` be a complex representation of $`G` which is faithful, i.e., the corresponding map $`G \to GL(V)` is injective. Show that any irreducible representation of $`G` occurs inside $`S^nV` (and hence inside $`V^{\otimes n}`) for some $`n`.

Hint: Show that there exists a vector $`u \in V^*` whose stabilizer in $`G` is 1. Now define the map $`SV \to F(G, \mathbb{C})` sending a polynomial $`f` on $`V^*` to the function $`f_u` on $`G` given by $`f_u(g) = f(gu)`. Show that this map is surjective and use this to deduce the desired result.

## Formalization
%%%
tag := "Chapter4/Problem4.12.10/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.RepresentationPolynomialFunctions.exists_nonzero_symmetric_power_intertwiner}

{Manual.docstring RepresentationTheory.RepresentationPolynomialFunctions.exists_surjective_equivariant_graded_map}

{Manual.docstring RepresentationTheory.TensorPowerRepresentations.exists_nonzero_intertwiner_to_tensorPower_of_injective}

### Supporting declarations

{Manual.docstring RepresentationTheory.RepresentationPolynomialFunctions.gradedMatrixCoefficient}
