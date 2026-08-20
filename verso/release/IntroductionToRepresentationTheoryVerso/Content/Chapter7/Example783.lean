/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter7.Example783

#doc (Manual) "Split exact sequence" =>

# Split exact sequence
%%%
tag := "Chapter7/Example7.8.3"
number := false
%%%

*Example 7.8.3.* The sequence $`0 \to X \to X \oplus Z \to Z \to 0` with the obvious morphisms is a short exact sequence. Such a sequence is called *split*. It corresponds to the trivial extension of $`Z` by $`X`.

## Formalization
%%%
tag := "Chapter7/Example7.8.3/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.CategoryTheory.ShortComplex.Biproduct.biproductShortComplexSplitting}

{Manual.docstring RepresentationTheory.CategoryTheory.ShortComplex.Biproduct.biproductShortComplex_shortExact}
