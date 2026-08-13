/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter7.Definition782

#doc (Manual) "Short exact sequence" =>

# Short exact sequence
%%%
tag := "Chapter7/Definition7.8.2"
number := false
%%%

*Definition 7.8.2.* A *short exact sequence* is an exact sequence of the form

$$`0 \to X \to Y \to Z \to 0.`

Clearly, $`0 \to X \to Y \to Z \to 0` is a short exact sequence if and only if $`X \to Y` is injective, $`Y \to Z` is surjective, and the induced map $`Y/X \to Z` is an isomorphism. In other words, short exact sequences correspond to extensions of $`Z` by $`X`.

## Formalization
%%%
tag := "Chapter7/Definition7.8.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.CategoryTheory.ShortComplex.Auxiliary.Data.toZeroMorphismsData}

{Manual.docstring RepresentationTheory.CategoryTheory.ShortComplex.Auxiliary.shortExact_iff_mono_epi_isIso_cokernelDesc}

### Supporting declarations

{Manual.docstring RepresentationTheory.CategoryTheory.ShortComplex.Auxiliary.Data}

{Manual.docstring RepresentationTheory.CategoryTheory.ShortComplex.Auxiliary.ZeroMorphismsData}

{Manual.docstring RepresentationTheory.CategoryTheory.ShortComplex.Auxiliary.ZeroMorphismsData.toData'}
