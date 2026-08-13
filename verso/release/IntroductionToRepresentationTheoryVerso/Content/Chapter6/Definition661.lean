/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter6.Definition661

#doc (Manual) "Definition 6.6.1: Sink and source" =>

# Definition 6.6.1: Sink and source
%%%
tag := "Chapter6/Definition6.6.1"
number := false
%%%

*Definition 6.6.1.* Let $`Q` be any quiver. We call a vertex $`i \in Q` a *sink* if all edges connected to $`i` point towards $`i`:

$$`\begin{array}{ccc} \longrightarrow & \overset{i}{\bullet} & \longleftarrow \\ & \uparrow & \end{array}.`

We call a vertex $`i \in Q` a *source* if all edges connected to $`i` point away from $`i`:

$$`\begin{array}{ccc} \longleftarrow & \overset{i}{\bullet} & \longrightarrow \\ & \downarrow & \end{array}.`

## Formalization
%%%
tag := "Chapter6/Definition6.6.1/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.QuiverVertexPredicates.vertexCondition}

{Manual.docstring RepresentationTheory.QuiverVertexPredicates.vertexProperty}
