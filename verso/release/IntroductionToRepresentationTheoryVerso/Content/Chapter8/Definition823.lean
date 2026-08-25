/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter8.Definition823

#doc (Manual) "Tor functors" =>

# Tor functors
%%%
tag := "Chapter8/Definition8.2.3"
number := false
%%%

*Definition 8.2.3.* Let $`M` be a right $`A`-module, $`P_\bullet` a projective resolution of $`M`, and $`N` a left $`A`-module. For $`i \geq 0` we define $`\mathrm{Tor}_i^A(M, N) = \mathrm{Tor}_i(M, N)` to be the $`i`th cohomology of the complex

$$`\cdots \to P_2 \otimes_A N \to P_1 \otimes_A N \to P_0 \otimes_A N \to 0`

induced by the resolution $`P_\bullet`.

## Formalization
%%%
tag := "Chapter8/Definition8.2.3/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupIsoResolutionHomology}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroup}

{Manual.docstring RepresentationTheory.Algebra.Homology.TensorProductConstruction.degreewiseModuleGroupFunctor}

{Manual.docstring RepresentationTheory.Algebra.Homology.TensorProductConstruction.moduleConstructionFunctor}
