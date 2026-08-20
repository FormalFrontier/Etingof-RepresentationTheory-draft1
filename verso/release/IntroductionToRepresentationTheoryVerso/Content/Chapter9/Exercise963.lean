/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter9.Exercise963

#doc (Manual) "Characterization of projective generators in finite abelian categories" =>

# Characterization of projective generators in finite abelian categories
%%%
tag := "Chapter9/Exercise9.6.3"
number := false
%%%

*Exercise 9.6.3.* Show that in a finite abelian category, $`P` is a projective generator if and only if for every simple object $`L`, one has $`\operatorname{Hom}(P, L) \neq 0`. Deduce that any finite abelian category has a projective generator.

## Formalization
%%%
tag := "Chapter9/Exercise9.6.3/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.CategoryTheory.Projective.Auxiliary.exists_object_with_nonempty_auxiliary}

{Manual.docstring RepresentationTheory.CategoryTheory.Projective.Auxiliary.nonempty_auxiliary_iff_forall_simple_exists_ne_zero}
