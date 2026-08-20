/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Definition288

#doc (Manual) "Subrepresentation of a quiver representation" =>
# Subrepresentation of a quiver representation
%%%
tag := "Chapter2/Definition2.8.8"
number := false
%%%
**Definition 2.8.8.** A **subrepresentation** of a representation $`(V_i, x_h)` of a quiver $`Q` is a representation $`(W_i, x'_h)` where $`W_i \subseteq V_i` for all $`i \in I` and where $`x_h(W_{h'}) \subseteq W_{h''}` and $`x'_h = x_h|_{W_{h'}} : W_{h'} \longrightarrow W_{h''}` for all $`h \in E`.

## Formalization
%%%
tag := "Chapter2/Definition2.8.8/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.CategoryTheory.QuiverAuxiliary.AuxiliaryType}

{Manual.docstring RepresentationTheory.CategoryTheory.QuiverAuxiliary.AuxiliaryType.toDiagram}
