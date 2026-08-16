/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter6.Definition663

#doc (Manual) "Definition 6.6.3: Reflection functor F\\_i^+" =>

# Definition 6.6.3: Reflection functor F\_i^+
%%%
tag := "Chapter6/Definition6.6.3"
number := false
%%%

*Definition 6.6.3.* Let $`Q` be a quiver, and let $`i \in Q` be a sink. Let $`V` be a representation of $`Q`. Then we define the reflection functor

$$`F_i^+ : \operatorname{Rep} Q \to \operatorname{Rep} \overline{Q}_i`

by the rule

$$`F_i^+(V)_k = V_k \quad \text{if } k \neq i,`

$$`F_i^+(V)_i = \ker\left(\varphi : \bigoplus_{j \to i} V_j \to V_i\right).`

## Formalization
%%%
tag := "Chapter6/Definition6.6.3/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.QuiverRepresentationAuxiliaryFunctor.auxiliaryRepresentationFunctor}
