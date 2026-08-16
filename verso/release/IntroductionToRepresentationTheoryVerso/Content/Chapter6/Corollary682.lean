/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter6.Corollary682

#doc (Manual) "Corollary 6.8.2: Dimension vector of indecomposable is a positive root" =>

# Corollary 6.8.2: Dimension vector of indecomposable is a positive root
%%%
tag := "Chapter6/Corollary6.8.2"
number := false
%%%

*Corollary 6.8.2.* _Let $`Q` be a quiver, and let $`V` be any indecomposable representation. Then $`d(V)` is a positive root._

*Proof.* By the proof of Theorem 6.8.1

$$`s_{i_1} \ldots s_{i_m} (d(V)) = \alpha_p.`

Since the $`s_i` preserve $`B`, we get

$$`B(d(V), d(V)) = B(\alpha_p, \alpha_p) = 2.`

$`\square`

## Formalization
%%%
tag := "Chapter6/Corollary6.8.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.AuxiliaryQuiverConstructions.auxiliary_property_finrank}
