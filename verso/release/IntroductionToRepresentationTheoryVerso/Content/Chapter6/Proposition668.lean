/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter6.Proposition668

#doc (Manual) "Proposition 6.6.8: Dimension vector under reflection is s\\_i(d(V))" =>

# Proposition 6.6.8: Dimension vector under reflection is s\_i(d(V))
%%%
tag := "Chapter6/Proposition6.6.8"
number := false
%%%

*Proposition 6.6.8.* _Let $`Q` be a quiver and let $`V` be a representation of $`Q`._

_(1) Let $`i \in Q` be a sink and let $`V` be surjective at $`i`. Then_

$$`
d(F_i^+ V) = s_i(d(V)).
`

_(2) Let $`i \in Q` be a source and let $`V` be injective at $`i`. Then_

$$`
d(F_i^- V) = s_i(d(V)).
`

*Proof.* We only prove the first statement; the second one follows similarly. Let $`i \in Q` be a sink and let

$$`
\varphi : \bigoplus_{j \to i} V_j \to V_i
`

be surjective. Let $`K = \ker \varphi`. Then

$$`
\dim K = \sum_{j \to i} \dim V_j - \dim V_i.
`

Therefore we get

$$`
\left( d(F_i^+ V) - d(V) \right)_i = \sum_{j \to i} \dim V_j - 2 \dim V_i = -B(d(V), \alpha_i)
`

and

$$`
\left( d(F_i^+ V) - d(V) \right)_j = 0, \quad j \neq i.
`
This implies

$$`
d(F_i^+ V) - d(V) = -B(d(V), \alpha_i) \alpha_i
`

$$`
\iff d(F_i^+ V) = d(V) - B(d(V), \alpha_i) \alpha_i = s_i(d(V)).
`

$`\square`

## Formalization
%%%
tag := "Chapter6/Proposition6.6.8/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryNatCast_eq_auxiliaryInt_of_injective}

{Manual.docstring RepresentationTheory.Quiver.AuxiliaryNatInt.Quiver.Auxiliary.auxiliaryNatCast_eq_auxiliaryInt_of_surjective}
