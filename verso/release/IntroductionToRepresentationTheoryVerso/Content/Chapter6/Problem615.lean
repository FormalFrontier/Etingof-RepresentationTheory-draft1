/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter6.Problem615

#doc (Manual) "Problem 6.1.5: Finite type quivers" =>

# Problem 6.1.5: Finite type quivers
%%%
tag := "Chapter6/Problem6.1.5"
number := false
%%%

*Problem 6.1.5.* Let $`Q` be a quiver with a set of vertices $`D`. We say that $`Q` is of *finite type* if it has finitely many indecomposable representations. Let $`b_{ij}` be the number of directed edges from $`i` to $`j` in $`Q` ($`i, j \in D`).

We have the following remarkable theorem, proved by P. Gabriel in the early 1970s.

## Formalization
%%%
tag := "Chapter6/Problem6.1.5/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.GraphTheory.ConnectedZeroOneAdjacency.PosDefCriterion.iff_of_symmetric_zeroOne_walkConnected}

### Supporting declarations

{Manual.docstring RepresentationTheory.Quiver.Finite.IsAdjacencyMatrix}
