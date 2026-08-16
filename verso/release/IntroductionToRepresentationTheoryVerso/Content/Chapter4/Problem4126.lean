/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter4.Problem4126

#doc (Manual) "Representations of affine group over finite field" =>

# Representations of affine group over finite field
%%%
tag := "Chapter4/Problem4.12.6"
number := false
%%%

**Problem 4.12.6.** Let $`\mathbb{F}_q` be a finite field with $`q` elements, and let $`G` be the group of nonconstant inhomogeneous linear transformations, $`x \to ax + b`, over $`\mathbb{F}_q` (i.e., $`a \in \mathbb{F}_q^{\times}`, $`b \in \mathbb{F}_q`). Find all irreducible complex representations of $`G`, and compute their characters. Compute the tensor products of irreducible representations.

Hint: Let $`V` be the representation of $`G` on the space of functions on $`\mathbb{F}_q` with sum of all values equal to zero. Show that $`V` is an irreducible representation of $`G`.

## Formalization
%%%
tag := "Chapter4/Problem4.12.6/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.AffineGroupRepresentations.cardinalityFormula_011270}

{Manual.docstring RepresentationTheory.AffineGroupRepresentations.cardinalityFormula_011306}

### Supporting declarations

{Manual.docstring RepresentationTheory.AffineGroupRepresentations.cardinalityFormula_011354}

{Manual.docstring RepresentationTheory.AffineGroupRepresentations.characterFormula_011257}

{Manual.docstring RepresentationTheory.AffineGroupRepresentations.membershipCharacterization_011454}

{Manual.docstring RepresentationTheory.AffineGroupRepresentations.simpleRepresentation_011343}
