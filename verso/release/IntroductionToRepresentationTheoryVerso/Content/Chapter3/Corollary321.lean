/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.Corollary321

#doc (Manual) "Any linear map on linearly independent vectors is realized by an algebra element" =>
# Any linear map on linearly independent vectors is realized by an algebra element
%%%
tag := "Chapter3/Corollary3.2.1"
number := false
%%%
**Corollary 3.2.1.** _Let $`V` be an irreducible finite dimensional representation of $`A`, and let $`v_1, \ldots, v_n \in V` be any linearly independent vectors. Then for any $`w_1, \ldots, w_n \in V` there exists an element $`a \in A` such that $`av_i = w_i` for all $`i`._

**Proof.** Assume the contrary. Then the image of the map $`A \to nV` given by $`a \mapsto (av_1, \ldots, av_n)` is a proper subrepresentation, so by Proposition 3.1.4 it corresponds to an $`r \times n` matrix $`X`, $`r < n`. Thus, taking $`a = 1`, we see that there exist vectors $`u_1, \ldots, u_r \in V` such that $`(u_1, \ldots, u_r)X = (v_1, \ldots, v_n)`. Let $`(q_1, \ldots, q_n)` be a nonzero vector such that $`X(q_1, \ldots, q_n)^T = 0` (it exists because $`r < n`). Then $`\sum q_i v_i = (u_1, \ldots, u_r)X(q_1, \ldots, q_n)^T = 0`, i.e. $`\sum q_i v_i = 0` — a contradiction to the linear independence of $`v_i`. $`\square`

## Formalization
%%%
tag := "Chapter3/Corollary3.2.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.RingTheory.SimpleModuleSimultaneousAction.exists_smul_eq_on_linearIndependent}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.Module.IsotypicDecomposition.exists_linearIndependent_coordinates_pi}

{Manual.docstring RepresentationTheory.Algebra.Module.SimpleScalarSurjectivity.algebra_smul_surjective}
