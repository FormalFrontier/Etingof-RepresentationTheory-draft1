/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Definition283

#doc (Manual) "Representation of a quiver" =>
# Representation of a quiver
%%%
tag := "Chapter2/Definition2.8.3"
number := false
%%%
**Definition 2.8.3.** A **representation of a quiver** $`Q` is an assignment to each vertex $`i \in I` of a vector space $`V_i` and to each edge $`h \in E` of a linear map $`x_h : V_{h'} \longrightarrow V_{h''}`.

## Formalization
%%%
tag := "Chapter2/Definition2.8.3/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData}
