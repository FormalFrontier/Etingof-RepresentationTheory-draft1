/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Proposition5222

#doc (Manual) "L\\_\\{lambda+1^N\\} \u2245 L\\_lambda \u2297 \u039b^N V" =>

# L\_\{lambda+1^N\} ≅ L\_lambda ⊗ Λ^N V
%%%
tag := "Chapter5/Proposition5.22.2"
number := false
%%%

*Proposition 5.22.2.* _The representation $`L_{\lambda + 1^N}` (where $`1^N = (1, 1, \ldots, 1) \in \mathbb{Z}^N`) is isomorphic to $`L_\lambda \otimes \wedge^N V`._

*Proof.* Indeed, $`L_\lambda \otimes \wedge^N V \subset V^{\otimes n} \otimes \wedge^N V \subset V^{\otimes n+N}`, and the only component of $`V^{\otimes n+N}` that has the same character as $`L_\lambda \otimes \wedge^N V` is $`L_{\lambda + 1^N}`. This implies the statement. $`\square`

## Formalization
%%%
tag := "Chapter5/Proposition5.22.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.GeneralLinearGroup.ExteriorPower.auxiliaryFiniteDimensionalRepresentationsIso}

{Manual.docstring RepresentationTheory.GeneralLinearGroup.ExteriorPower.exteriorPowerRepresentation_apply}

{Manual.docstring RepresentationTheory.GeneralLinearGroup.ExteriorPower.shiftedAuxiliaryRepresentationTensorAuxiliaryIsoNonempty}

{Manual.docstring RepresentationTheory.GeneralLinearGroup.ExteriorPower.shiftedAuxiliaryRepresentationTensorIsoNonempty}
