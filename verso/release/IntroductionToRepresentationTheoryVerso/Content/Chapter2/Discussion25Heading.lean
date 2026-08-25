/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Discussion25Heading

#doc (Manual) "Section 2.5 Quotients \u2014 heading and definition of quotient algebra" =>
# Section 2.5 Quotients — heading and definition of quotient algebra
%%%
tag := "Chapter2/Discussion_2.5_heading"
number := false
%%%

## 2.5. Quotients
%%%
tag := "Chapter2/Discussion_2.5_heading/heading-1"
%%%

Let $`A` be an algebra and let $`I` be a two-sided ideal in $`A`. Then $`A/I` is the set of (additive) cosets of $`I`. Let $`\pi : A \to A/I` be the quotient map. We can define multiplication in $`A/I` by $`\pi(a) \cdot \pi(b) := \pi(ab)`.

## Formalization
%%%
tag := "Chapter2/Discussion_2.5_heading/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.RingTheory.Quotient.Constructions.TwoSidedIdeal.auxiliaryAlgHom}

{Manual.docstring RepresentationTheory.RingTheory.Quotient.Constructions.TwoSidedIdeal.auxiliaryAlgHom_eq_iff}

{Manual.docstring RepresentationTheory.RingTheory.Quotient.Constructions.TwoSidedIdeal.auxiliaryAlgHom_mul}

### Supporting declarations

{Manual.docstring RepresentationTheory.RingTheory.Quotient.Constructions.TwoSidedIdeal.AuxiliaryType}
