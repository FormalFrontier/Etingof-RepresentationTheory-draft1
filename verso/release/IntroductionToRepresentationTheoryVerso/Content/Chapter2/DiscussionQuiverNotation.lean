/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.DiscussionQuiverNotation

#doc (Manual) "Notation for vertices and edges of quivers" =>
# Notation for vertices and edges of quivers
%%%
tag := "Chapter2/Discussion_quiver_notation"
number := false
%%%
We denote the set of vertices of the quiver $`Q` as $`I` and the set of edges as $`E`. For an edge $`h \in E`, let $`h'`, $`h''` denote the source and target of $`h`, respectively:

$$`\bullet_{h'} \xrightarrow{h} \bullet_{h''}`

## Formalization
%%%
tag := "Chapter2/Discussion_quiver_notation/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Quiver.Arrows.Arrow.source}

{Manual.docstring RepresentationTheory.Quiver.Arrows.Arrow.target}

### Supporting declarations

{Manual.docstring RepresentationTheory.Quiver.Arrows.Arrow}

{Manual.docstring RepresentationTheory.Quiver.Arrows.Arrow.hom}
