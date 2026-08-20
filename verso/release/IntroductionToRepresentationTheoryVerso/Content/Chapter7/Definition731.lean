/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter7.Definition731

#doc (Manual) "Natural transformation" =>

# Natural transformation
%%%
tag := "Chapter7/Definition7.3.1"
number := false
%%%

*Definition 7.3.1.* Let $`\mathcal{C}, \mathcal{D}` be categories and let $`F, G : \mathcal{C} \to \mathcal{D}` be functors between them. A morphism $`a : F \to G` (also called a *natural transformation* or a *functorial morphism*) is a collection of morphisms $`a_X : F(X) \to G(X)` labeled by the objects $`X` of $`\mathcal{C}`, which is functorial in $`X`; i.e., for any morphism $`f : X \to Y` (for $`X, Y \in \mathcal{C}`) one has $`a_Y \circ F(f) = G(f) \circ a_X`.

A morphism $`a : F \to G` is an isomorphism if there is another morphism $`a^{-1} : G \to F` such that $`a \circ a^{-1}` and $`a^{-1} \circ a` are the identities. The set of morphisms from $`F` to $`G` is denoted by $`\operatorname{Hom}(F, G)`.

## Formalization
%%%
tag := "Chapter7/Definition7.3.1/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.FunctorPairConstructions.associatedType}
