/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Definition2141

#doc (Manual) "Tensor product of Lie algebra representations" =>
# Tensor product of Lie algebra representations
%%%
tag := "Chapter2/Definition2.14.1"
number := false
%%%
**Definition 2.14.1.** The **tensor product** of two representations $`V, W` of a Lie algebra $`\mathfrak{g}` is the space $`V \otimes W` with

$$`\rho_{V \otimes W}(x) = \rho_V(x) \otimes \operatorname{Id} + \operatorname{Id} \otimes \rho_W(x).`

## Formalization
%%%
tag := "Chapter2/Definition2.14.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Lie.AuxiliaryTwoModuleType.AuxiliaryLieModuleType.lie_bracket_tmul}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.Lie.AuxiliaryTwoModuleType.AuxiliaryLieModuleType}
