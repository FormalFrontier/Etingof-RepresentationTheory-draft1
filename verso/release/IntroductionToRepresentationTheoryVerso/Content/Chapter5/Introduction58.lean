/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Introduction58

#doc (Manual) "Section 5.8: Induced representations \u2014 restriction and induction" =>

# Section 5.8: Induced representations — restriction and induction
%%%
tag := "Chapter5/Introduction_5.8"
number := false
%%%

## 5.8. Induced representations
%%%
tag := "Chapter5/Introduction_5.8/heading-1"
%%%

Given a representation $`V` of a group $`G` and a subgroup $`H \subset G`, there is a natural way to construct a representation of $`H`. The **restriction** of $`V` to $`H`, $`\operatorname{Res}_H^G V` is the representation given by the vector space $`V`, and the action $`\rho_{\operatorname{Res}_H^G V} = \rho_V|_H`.

There is also a natural, but less trivial, way to construct a representation of a group $`G` given a representation $`V` of its subgroup $`H`.

## Formalization
%%%
tag := "Chapter5/Introduction_5.8/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.InductionAndCoinduction.coinduced}

{Manual.docstring RepresentationTheory.InductionAndCoinduction.finiteIndexInduced}
