/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter7.Exercise784

#doc (Manual) "Exact sequences of vector spaces split" =>

# Exact sequences of vector spaces split
%%%
tag := "Chapter7/Exercise7.8.4"
number := false
%%%

*Exercise 7.8.4.* Show that any exact sequence of vector spaces is isomorphic to a direct sum of complexes of the form

$$`0 \to V \to V \to 0,`

where $`V` stands at the places $`i` and $`i + 1` and the map $`V \to V` is the identity (in particular, any short exact sequence of vector spaces is split). Is this true in the category of abelian groups?

## Formalization
%%%
tag := "Chapter7/Exercise7.8.4/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.HomologicalAlgebra.AcyclicComplexDecomposition.ShortComplex.nonempty_splitting_of_shortExact}

{Manual.docstring RepresentationTheory.HomologicalAlgebra.AcyclicComplexDecomposition.exists_acyclicComplexIso_sigmaTwoTermComplex}

### Supporting declarations

{Manual.docstring RepresentationTheory.HomologicalAlgebra.AcyclicComplexDecomposition.exists_shortExact_isEmpty_splitting}
