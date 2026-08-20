/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Discussion22Intro

#doc (Manual) "Section 2.2 heading and introduction to systematic discussion" =>
# Section 2.2 heading and introduction to systematic discussion
%%%
tag := "Chapter2/Discussion_2.2_intro"
number := false
%%%

## Section 2.2 heading and introduction to systematic discussion
%%%
tag := "Chapter2/Discussion_2.2_intro/heading-1"
number := false
%%%
Let us now begin a systematic discussion of representation theory.

Let $`k` be a field. Unless stated otherwise, we will always assume that $`k` is algebraically
closed, i.e., any nonconstant polynomial with coefficients in $`k` has a root in $`k`. The main
example is the field of complex numbers $`\mathbb{C}`, but we will also consider fields of
characteristic $`p`, such as the algebraic closure $`\overline{\mathbb{F}}_p` of the finite field
$`\mathbb{F}_p` of $`p` elements.

## Formalization
%%%
tag := "Chapter2/Discussion_2.2_intro/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.FieldTheory.IsAlgClosed.Basic.Complex.isAlgClosed}

{Manual.docstring RepresentationTheory.FieldTheory.IsAlgClosed.Basic.isAlgClosed_iff_nonconstant_root}

### Supporting declarations

{Manual.docstring RepresentationTheory.FieldTheory.IsAlgClosed.Basic.AlgebraicClosure.zmod_charP}

{Manual.docstring RepresentationTheory.FieldTheory.IsAlgClosed.Basic.AlgebraicClosure.zmod_isAlgClosed}

{Manual.docstring RepresentationTheory.FieldTheory.IsAlgClosed.Basic.ZMod.card_eq_prime}

{Manual.docstring RepresentationTheory.FieldTheory.IsAlgClosed.Basic.ZMod.fieldOfPrime}
