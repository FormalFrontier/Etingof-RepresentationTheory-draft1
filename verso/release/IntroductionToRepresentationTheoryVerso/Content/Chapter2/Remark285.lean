/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Remark285

#doc (Manual) "Path algebra of a finite quiver has a unit" =>
# Path algebra of a finite quiver has a unit
%%%
tag := "Chapter2/Remark2.8.5"
number := false
%%%
**Remark 2.8.5.** It is easy to see that if $`Q` is a finite set then $`\sum_{i \in I} p_i = 1`, so $`P_Q` is an algebra with unit.

## Formalization
%%%
tag := "Chapter2/Remark2.8.5/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.Quiver.AuxiliaryPathStructures.Quiver.AuxiliaryOppositeType.sum_auxiliaryVertexElement_eq_one}
