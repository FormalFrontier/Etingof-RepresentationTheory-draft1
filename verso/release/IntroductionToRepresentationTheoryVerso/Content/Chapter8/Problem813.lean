/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter8.Problem813

#doc (Manual) "Flat modules" =>

# Flat modules
%%%
tag := "Chapter8/Problem8.1.3"
number := false
%%%

*Problem 8.1.3.* A right $`A`-module $`M` is said to be *flat* if the functor $`M \otimes_A` on the category of left $`A`-modules is exact.

(i) Show that any projective module is flat.

(ii) Let $`A` be a commutative ring and let $`S` be any multiplicatively closed subset of $`A`. Then, the localization $`S^{-1}A` is a flat $`A`-module.

(iii) Let $`A = \mathbb{C}[x]`, $`M = \mathbb{C}[x, x^{-1}]`. Show that $`M` is flat but not projective.

## Formalization
%%%
tag := "Chapter8/Problem8.1.3/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Homology.Flatness.Localization.flat}

{Manual.docstring RepresentationTheory.Algebra.Homology.Flatness.Module.Projective.oppositeRingModuleProperty}

{Manual.docstring RepresentationTheory.Algebra.Homology.Flatness.localizationAwayX_flat_not_projective}
