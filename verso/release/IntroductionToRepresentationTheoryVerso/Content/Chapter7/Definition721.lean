/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter7.Definition721

#doc (Manual) "Functor" =>

# Functor
%%%
tag := "Chapter7/Definition7.2.1"
number := false
%%%

*Definition 7.2.1.* A *functor* $`F : \mathcal{C} \to \mathcal{D}` between categories $`\mathcal{C}` and $`\mathcal{D}` is

(i) a map $`F : Ob(\mathcal{C}) \to Ob(\mathcal{D})`;
(ii) for each $`X, Y \in \mathcal{C}`, a map $`F = F_{X,Y} : \operatorname{Hom}(X, Y) \to \operatorname{Hom}(F(X), F(Y))` which preserves compositions and identity morphisms.

## Formalization
%%%
tag := "Chapter7/Definition7.2.1/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.CategoryPair.AssociatedType}
