/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter7.Definition771

#doc (Manual) "Abelian category" =>

# Abelian category
%%%
tag := "Chapter7/Definition7.7.1"
number := false
%%%

*Definition 7.7.1.* An *abelian category* is a category (enriched over the category of abelian groups) which is equivalent to a full subcategory $`\mathcal{C}` of the category $`A`-mod of left modules over a ring $`A`, closed under taking finite direct sums, as well as kernels, cokernels, and images of morphisms.

## Formalization
%%%
tag := "Chapter7/Definition7.7.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.AbelianCategoryRepresentation.categoryDataOfObjectProperty}

{Manual.docstring RepresentationTheory.AbelianCategoryRepresentation.exists_moduleCatFullSubcategoryEquivalence}
