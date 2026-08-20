/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter7.Example792

#doc (Manual) "Ind, Res, Hom as additive k-linear functors" =>

# Ind, Res, Hom as additive k-linear functors
%%%
tag := "Chapter7/Example7.9.2"
number := false
%%%

*Example 7.9.2.* The functors $`\operatorname{Ind}_K^G`, $`\operatorname{Res}_K^G`, $`\operatorname{Hom}_G(V, ?)` in the theory of group representations over a field $`k` are additive and $`k`-linear.

## Formalization
%%%
tag := "Chapter7/Example7.9.2/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.CategoryTheory.LinearFunctors.indFunctor_additive}

{Manual.docstring RepresentationTheory.CategoryTheory.LinearFunctors.indFunctor_linear}

{Manual.docstring RepresentationTheory.CategoryTheory.LinearFunctors.linearCoyoneda_obj_additive}

{Manual.docstring RepresentationTheory.CategoryTheory.LinearFunctors.linearCoyoneda_obj_linear}

{Manual.docstring RepresentationTheory.CategoryTheory.LinearFunctors.resFunctor_additive}

{Manual.docstring RepresentationTheory.CategoryTheory.LinearFunctors.resFunctor_linear}
