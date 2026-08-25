/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter6.Problem613ContinuedE7E8

#doc (Manual) "Problem 6.1.3 continued: E7, E8, and parts (a)-(e)" =>

# Problem 6.1.3 continued: E7, E8, and parts (a)-(e)
%%%
tag := "Chapter6/Problem6.1.3_continued_E7_E8"
number := false
%%%

* _$`E_7`:_

$$`\circ \text{---} \circ \text{---} \circ \text{---} \circ \text{---} \circ \text{---} \circ`

$$`\hspace{5em} |`

$$`\hspace{5em} \circ`

* _$`E_8`:_

$$`\circ \text{---} \circ \text{---} \circ \text{---} \circ \text{---} \circ \text{---} \circ \text{---} \circ`

$$`\hspace{5em} |`

$$`\hspace{5em} \circ`

(a) Compute the determinant of $`A` where $`\Gamma = A_n, D_n`. (Use the row decomposition rule, and write down a recursive equation for it.) Deduce by Sylvester criterion that $`A_n, D_n` are Dynkin diagrams.[^sylvester]

(b) Compute the determinants of $`A` for $`E_6, E_7, E_8` (use row decomposition and reduce to (a)). Show they are Dynkin diagrams.

(c) Show that if $`\Gamma` is a Dynkin diagram, it cannot have cycles. For this, show that $`\det(A) = 0` for a graph $`\Gamma` below:

$$`\overset{1}{\bullet} \text{---} \overset{1}{\bullet} \text{-} \cdots \text{-} \overset{1}{\bullet} \text{---} \overset{1}{\bullet}`

(a cycle with all vertices labeled 1).

(Show that the sum of rows is 0.) Thus $`\Gamma` has to be a tree.

(d) Show that if $`\Gamma` is a Dynkin diagram, it cannot have vertices with four or more incoming edges and that $`\Gamma` can have no more than one vertex with three incoming edges. For this, show that $`\det(A) = 0` for a graph $`\Gamma` below:

$$`\overset{1}{\bullet} \searrow \hspace{1em} \swarrow \overset{1}{\bullet}`

$$`\hspace{1.5em} \overset{2}{\bullet} \text{-} \cdots \text{-} \overset{2}{\bullet}`

$$`\overset{1}{\bullet} \nearrow \hspace{1em} \nwarrow \overset{1}{\bullet}`

(a graph where two vertices of degree $`\geq 3` are connected by a chain, each with two additional pendant edges labeled 1, and the chain vertices labeled 2).

(e) Show that $`\det(A) = 0` for all graphs $`\Gamma` below:


[^sylvester]: The Sylvester criterion says that a symmetric bilinear form $`( \,,\, )` on $`\mathbb{R}^n` is positive definite if and only if for any $`k \leq n`, $`\det_{1 \leq i,j \leq k}(e_i, e_j) > 0`.

## Formalization
%%%
tag := "Chapter6/Problem6.1.3_continued_E7_E8/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.DynkinDiagram.AffineClassification.AffineDynkinDiagram.det_two_smul_one_sub_adjacency_eq_zero}

{Manual.docstring RepresentationTheory.DynkinDiagram.AffineClassification.AffineDynkinDiagram.two_smul_one_sub_adjacency_mulVec_marks_eq_zero}

{Manual.docstring RepresentationTheory.DynkinDiagram.FiniteSimplyLaced.det_cartanMatrix_typeA}

{Manual.docstring RepresentationTheory.DynkinDiagram.FiniteSimplyLaced.det_cartanMatrix_typeD}

{Manual.docstring RepresentationTheory.DynkinDiagram.FiniteSimplyLaced.det_cartanMatrix_typeE6}

{Manual.docstring RepresentationTheory.DynkinDiagram.FiniteSimplyLaced.det_cartanMatrix_typeE7}

{Manual.docstring RepresentationTheory.DynkinDiagram.FiniteSimplyLaced.det_cartanMatrix_typeE8}

{Manual.docstring RepresentationTheory.DynkinDiagram.FiniteSimplyLaced.det_two_smul_one_sub_cycleAdjacencyMatrix_eq_zero}

{Manual.docstring RepresentationTheory.DynkinDiagram.FiniteSimplyLaced.eq_of_vertexDegree_eq_three_of_isFiniteSimplyLaced}

{Manual.docstring RepresentationTheory.DynkinDiagram.FiniteSimplyLaced.exceptionalTypes_areFiniteSimplyLaced}

{Manual.docstring RepresentationTheory.DynkinDiagram.FiniteSimplyLaced.sum_adjacency_entries_eq_twice_rank_sub_two_of_isFiniteSimplyLaced}

{Manual.docstring RepresentationTheory.DynkinDiagram.FiniteSimplyLaced.typeA_isFiniteSimplyLaced}

{Manual.docstring RepresentationTheory.DynkinDiagram.FiniteSimplyLaced.typeD_isFiniteSimplyLaced}

{Manual.docstring RepresentationTheory.DynkinDiagram.FiniteSimplyLaced.vertexDegree_le_three_of_isFiniteSimplyLaced}
