/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Definition2810

#doc (Manual) "Homomorphism of quiver representations" =>
# Homomorphism of quiver representations
%%%
tag := "Chapter2/Definition2.8.10"
number := false
%%%
**Definition 2.8.10.** Let $`(V_i, x_h)` and $`(W_i, y_h)` be representations of the quiver $`Q`. A **homomorphism** $`\varphi : (V_i) \longrightarrow (W_i)` of quiver representations is a collection of maps $`\varphi_i : V_i \longrightarrow W_i` such that $`y_h \circ \varphi_{h'} = \varphi_{h''} \circ x_h` for all $`h \in E`.

## Formalization
%%%
tag := "Chapter2/Definition2.8.10/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.CategoryTheory.QuiverLinearMaps.AuxiliaryQuiverLinearMapData}
