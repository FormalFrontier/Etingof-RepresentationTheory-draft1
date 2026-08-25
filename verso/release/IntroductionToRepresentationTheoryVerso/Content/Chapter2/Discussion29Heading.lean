/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Discussion29Heading

#doc (Manual) "Section 2.9: Lie algebras \u2014 heading and skew-symmetric bilinear map" =>
# Section 2.9: Lie algebras — heading and skew-symmetric bilinear map
%%%
tag := "Chapter2/Discussion_2.9_heading"
number := false
%%%

## 2.9. Lie algebras
%%%
tag := "Chapter2/Discussion_2.9_heading/heading-1"
%%%

Let $`\mathfrak{g}` be a vector space over a field $`k`, and let $`[\ ,\ ] : \mathfrak{g} \times \mathfrak{g} \longrightarrow \mathfrak{g}` be a skew-symmetric bilinear map. (That is, $`[a, a] = 0`, and hence $`[a, b] = -[b, a]`.)

## Formalization
%%%
tag := "Chapter2/Discussion_2.9_heading/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.LieAlgebra.BracketIdentities.bracket_eq_neg_bracket_swap}

{Manual.docstring RepresentationTheory.LieAlgebra.BracketIdentities.bracket_self}

### Supporting declarations

{Manual.docstring RepresentationTheory.LieAlgebra.BracketIdentities.bracket_add_left}

{Manual.docstring RepresentationTheory.LieAlgebra.BracketIdentities.bracket_add_right}

{Manual.docstring RepresentationTheory.LieAlgebra.BracketIdentities.bracket_smul_left}

{Manual.docstring RepresentationTheory.LieAlgebra.BracketIdentities.bracket_smul_right}
