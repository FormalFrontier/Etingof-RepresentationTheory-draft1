/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter6.Problem613ContinuedTildeE

#doc (Manual) "Problem 6.1.3 continued: affine Dynkin diagrams and parts (f)-(g)" =>

# Problem 6.1.3 continued: affine Dynkin diagrams and parts (f)-(g)
%%%
tag := "Chapter6/Problem6.1.3_continued_tildeE"
number := false
%%%

* _$`\tilde{E}_6`:_

$$`\overset{1}{\bullet} \text{---} \overset{2}{\bullet} \text{---} \overset{3}{\bullet} \text{---} \overset{2}{\bullet} \text{---} \overset{1}{\bullet}`

$$`\hspace{5em} |`

$$`\hspace{5em} \overset{2}{\bullet}`

$$`\hspace{5em} |`

$$`\hspace{5em} \overset{1}{\bullet}`

* _$`\tilde{E}_7`:_

$$`\overset{1}{\bullet} \text{---} \overset{2}{\bullet} \text{---} \overset{3}{\bullet} \text{---} \overset{4}{\bullet} \text{---} \overset{3}{\bullet} \text{---} \overset{2}{\bullet} \text{---} \overset{1}{\bullet}`

$$`\hspace{7em} |`

$$`\hspace{7em} \overset{2}{\bullet}`

* _$`\tilde{E}_8`:_

$$`\overset{1}{\bullet} \text{---} \overset{2}{\bullet} \text{---} \overset{3}{\bullet} \text{---} \overset{4}{\bullet} \text{---} \overset{5}{\bullet} \text{---} \overset{6}{\bullet} \text{---} \overset{4}{\bullet} \text{---} \overset{2}{\bullet}`

$$`\hspace{9em} |`

$$`\hspace{9em} \overset{3}{\bullet}`

_Hint for (c)-(e):_ What is the meaning of the numbers labeling the vertices of these graphs?

(f) Deduce from (a)—(e) the classification theorem for Dynkin diagrams.

(g) A (simply laced) *affine Dynkin diagram* is a connected graph without self-loops such that the quadratic form defined by $`A` is positive semidefinite but not positive definite. Classify affine Dynkin diagrams. (Show that they are exactly the forbidden diagrams from (c)—(e).)

## Formalization
%%%
tag := "Chapter6/Problem6.1.3_continued_tildeE/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.DynkinDiagram.AffineClassification.AffineDynkinDiagram.adjacency_isAffineDynkinMatrix}

{Manual.docstring RepresentationTheory.DynkinDiagram.AffineClassification.AffineDynkinDiagram.det_two_smul_one_sub_adjacency_eq_zero}

{Manual.docstring RepresentationTheory.DynkinDiagram.AffineClassification.AffineDynkinDiagram.two_smul_one_sub_adjacency_mulVec_marks_eq_zero}

{Manual.docstring RepresentationTheory.DynkinDiagram.AffineClassification.isAffineDynkinMatrix_iff_exists_equiv}

{Manual.docstring RepresentationTheory.DynkinDiagram.AffineClassification.isFiniteDynkinMatrix_iff_exists_equiv}
