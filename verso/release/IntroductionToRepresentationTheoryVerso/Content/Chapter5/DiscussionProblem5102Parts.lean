/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.DiscussionProblem5102Parts

#doc (Manual) "Problem 5.10.2 parts (a)-(f): tensor products over k-algebras for Ind and Res" =>

# Problem 5.10.2 parts (a)-(f): tensor products over k-algebras for Ind and Res
%%%
tag := "Chapter5/Discussion_Problem5.10.2_parts"
number := false
%%%

new proof of the Frobenius reciprocity and to some analogies between induction and restriction.

Throughout this exercise, we will use the notation and results of Problem 2.11.6.

Let $`G` be a finite group and $`H \subset G` a subgroup. We consider $`k[G]` as a $`(k[H], k[G])`-bimodule (both module structures are given by multiplication inside $`k[G]`). We denote this bimodule by $`k[G]_1`. On the other hand, we can also consider $`k[G]` as a $`(k[G], k[H])`-bimodule (again, both module structures are given by multiplication). We denote this bimodule by $`k[G]_2`.

(a) Let $`V` be a representation of $`G`. Then, $`V` is a left $`k[G]`-module. Thus, the tensor product $`k[G]_1 \otimes_{k[G]} V` is a left $`k[H]`-module. Prove that this tensor product is isomorphic to $`\operatorname{Res}_H^G V` as a left $`k[H]`-module. The isomorphism

$$`\operatorname{Res}_H^G V \to k[G]_1 \otimes_{k[G]} V`

is given by $`v \mapsto 1 \otimes_{k[G]} v` for every $`v \in \operatorname{Res}_H^G V`.

(b) Let $`W` be a representation of $`H`. Then $`W` is a left $`k[H]`-module. According to Remark 5.8.2, $`\operatorname{Ind}_H^G W \cong \operatorname{Hom}_H(k[G], W)`. In other words, we have $`\operatorname{Ind}_H^G W \cong \operatorname{Hom}_{k[H]}(k[G]_1, W)`. Now use part (b) of Problem 2.11.6 to conclude Theorem 5.10.1.

(c) Let $`V` be a representation of $`G`. Then, $`V` is a left $`k[G]`-module. Prove that not only $`k[G]_1 \otimes_{k[G]} V` but also $`\operatorname{Hom}_{k[G]}(k[G]_2, V)` is isomorphic to $`\operatorname{Res}_H^G V` as a left $`k[H]`-module. The isomorphism

$$`\operatorname{Hom}_{k[G]}(k[G]_2, V) \to \operatorname{Res}_H^G V`

is given by $`f \mapsto f(1)` for every $`f \in \operatorname{Hom}_{k[G]}(k[G]_2, V)`.

(d) Let $`W` be a representation of $`H`. Then, $`W` is a left $`k[H]`-module. Show that $`\operatorname{Ind}_H^G W` is isomorphic to $`k[G]_2 \otimes_{k[H]} W`. The isomorphism $`\operatorname{Hom}_{k[H]}(k[G]_1, W) \to k[G]_2 \otimes_{k[H]} W` is given by $`f \mapsto \sum_{g \in P} g^{-1} \otimes_{k[H]} f(g)` for every $`f \in \operatorname{Hom}_{k[H]}(k[G]_1, W)`, where $`P` is a set of distinct representatives for the right $`H`-cosets in $`G`. (This isomorphism is independent of the choice of representatives.)

(e) Let $`V` be a representation of $`G` and let $`W` be a representation of $`H`. Use (b) to prove that $`\operatorname{Hom}_G(\operatorname{Ind}_H^G W, V)` is naturally isomorphic to $`\operatorname{Hom}_H(W, \operatorname{Res}_H^G V)`.
(f) Let $`V` be a representation of $`H`. Prove that $`\operatorname{Ind}_H^G(V^*) \cong \left(\operatorname{Ind}_H^G V\right)^*` as representations of $`G`. \[Hint: Write $`\operatorname{Ind}_H^G V` as $`k[G]_2 \otimes_{k[H]} V` and write $`\operatorname{Ind}_H^G(V^*)` as $`\operatorname{Hom}_{k[H]}(k[G]_1, V^*)`. Prove that the map $`\operatorname{Hom}_{k[H]}(k[G]_1, V^*) \times \left(\operatorname{Ind}_H^G(V)\right) \to k` given by $`(f, (x \otimes_{k[H]} v)) \mapsto (f(Sx))(v)` is a nondegenerate $`G`-invariant bilinear form, where $`S : k[G] \to k[G]` is the linear map defined by $`Sg = g^{-1}` for every $`g \in G`.\]

## Formalization
%%%
tag := "Chapter5/Discussion_Problem5.10.2_parts/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.InductionCoinduction.finiteGroupFDRepAuxiliaryDualIso}

{Manual.docstring RepresentationTheory.InductionCoinduction.indResAdjunction}

{Manual.docstring RepresentationTheory.Subgroup.HomAdjunction.ambientSubgroupHomEquiv}

### Supporting declarations

{Manual.docstring RepresentationTheory.InductionCoinduction.coindIsoIndOfFinite}

{Manual.docstring RepresentationTheory.InductionCoinduction.coindIsoIndOfFinite_hom_apply}

{Manual.docstring RepresentationTheory.InductionCoinduction.indResHomLinearEquiv}

{Manual.docstring RepresentationTheory.InductionCoinduction.restrictCoindIdIso}

{Manual.docstring RepresentationTheory.InductionCoinduction.restrictCoindIdIso_hom_apply}

{Manual.docstring RepresentationTheory.InductionCoinduction.restrictIndIdIso}

{Manual.docstring RepresentationTheory.InductionCoinduction.restrictIndIdIso_inv_apply}

{Manual.docstring RepresentationTheory.Subgroup.HomAdjunction.ambientSubgroupHomFunctorIso}
