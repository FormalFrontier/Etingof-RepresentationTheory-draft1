/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter7.DiscussionAfterDefinition791

#doc (Manual) "Additive functors preserve direct sums" =>

# Additive functors preserve direct sums
%%%
tag := "Chapter7/Discussion_after_Definition7.9.1"
number := false
%%%

It is easy to show that if $`F` is an additive functor, then $`F(X \oplus Y)` is canonically isomorphic to $`F(X) \oplus F(Y)`.

## Formalization
%%%
tag := "Chapter7/Discussion_after_Definition7.9.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Preadditive.FunctorProperties.PreadditiveProperty.binaryBiproductComparisonIso}
