/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter8.Exercise829

#doc (Manual) "Categories without enough projectives" =>

# Categories without enough projectives
%%%
tag := "Chapter8/Exercise8.2.9"
number := false
%%%

*Exercise 8.2.9.* (i) Show that the category of finite abelian groups or finite dimensional $`k[x]`-modules does not contain nonzero projective objects (so it does not have enough projectives).

(ii) Let $`A` be a finitely generated commutative ring. Show that the category of finitely generated $`A`-modules has enough projectives.

## Formalization
%%%
tag := "Chapter8/Exercise8.2.9/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Module.Lifting.subsingleton_of_lifts_along_surjective_addMonoidHoms}

{Manual.docstring RepresentationTheory.Algebra.Module.Lifting.subsingleton_of_lifts_along_surjective_polynomialLinearMaps}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.Module.Lifting.exists_surjective_finFreeLinearMap_of_finite}
