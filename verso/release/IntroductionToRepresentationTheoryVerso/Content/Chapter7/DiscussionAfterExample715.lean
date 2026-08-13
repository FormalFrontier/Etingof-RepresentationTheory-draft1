/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter7.DiscussionAfterExample715

#doc (Manual) "Enriched categories" =>

# Enriched categories
%%%
tag := "Chapter7/Discussion_after_Example7.1.5"
number := false
%%%

Sometimes the collection $`\operatorname{Hom}(X, Y)` of morphisms from $`X` to $`Y` in a given locally small category $`\mathcal{C}` is not just a set but has some additional structure (say, the structure of an abelian group, or a vector space over some field). In this case one says that $`\mathcal{C}` is *enriched* over another category $`\mathcal{D}` (which is a *monoidal* category, i.e., has a product operation and a unit object under this product, e.g., the category of abelian groups or vector spaces with the tensor product operation). This means that for each $`X, Y \in \mathcal{C}`, $`\operatorname{Hom}(X, Y)` is an object of $`\mathcal{D}`, and the composition $`\operatorname{Hom}(Y, Z) \times \operatorname{Hom}(X, Y) \to \operatorname{Hom}(X, Z)` is a morphism in $`\mathcal{D}`. E.g., if $`\mathcal{D}` is the category of vector spaces, this means that the composition is bilinear, i.e., gives rise to a linear map $`\operatorname{Hom}(Y, Z) \otimes \operatorname{Hom}(X, Y) \to \operatorname{Hom}(X, Z)`. For a more detailed discussion of this, we refer the reader to \[*McL*\].

## Formalization
%%%
tag := "Chapter7/Discussion_after_Example7.1.5/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.CategoryTheory.EnrichedCorepresentability.AuxiliaryMonoidalTypeOperator}

{Manual.docstring RepresentationTheory.CategoryTheory.EnrichedCorepresentability.enrichedComposition}
