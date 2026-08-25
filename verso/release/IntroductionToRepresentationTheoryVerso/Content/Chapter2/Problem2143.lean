/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Problem2143

#doc (Manual) "Hom-tensor adjunction for Lie algebra representations" =>
# Hom-tensor adjunction for Lie algebra representations
%%%
tag := "Chapter2/Problem2.14.3"
number := false
%%%
**Problem 2.14.3.** Let $`V, W, U` be finite dimensional representations of a Lie algebra $`\mathfrak{g}`. Show that the space $`\operatorname{Hom}_{\mathfrak{g}}(V \otimes W, U)` is isomorphic to $`\operatorname{Hom}_{\mathfrak{g}}(V, U \otimes W^*)`. (Here $`\operatorname{Hom}_{\mathfrak{g}} := \operatorname{Hom}_{\mathcal{U}(\mathfrak{g})}`.)

## Formalization
%%%
tag := "Chapter2/Problem2.14.3/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.LieModule.HomTensorAdjunction.lieModuleHomTensorDualEquiv}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.Lie.UniversalEnveloping.representationAlgHomEquiv}
