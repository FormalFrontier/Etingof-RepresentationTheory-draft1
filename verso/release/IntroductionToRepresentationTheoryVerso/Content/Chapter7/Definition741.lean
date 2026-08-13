/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter7.Definition741

#doc (Manual) "Equivalence of categories" =>

# Equivalence of categories
%%%
tag := "Chapter7/Definition7.4.1"
number := false
%%%

*Definition 7.4.1.* A functor $`F : \mathcal{C} \to \mathcal{D}` is an *equivalence of categories* if there exists $`F' : \mathcal{D} \to \mathcal{C}` such that $`F \circ F'` and $`F' \circ F` are isomorphic to the identity functors.

In this situation, $`F'` is said to be a *quasi-inverse* to $`F`.

## Formalization
%%%
tag := "Chapter7/Definition7.4.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Categories.ParameterizedType}
