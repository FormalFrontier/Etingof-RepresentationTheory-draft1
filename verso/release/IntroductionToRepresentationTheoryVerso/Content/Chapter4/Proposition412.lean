/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter4.Proposition412

#doc (Manual) "Semisimplicity of k\\[G\\] implies characteristic does not divide |G|" =>

# Semisimplicity of k\[G\] implies characteristic does not divide |G|
%%%
tag := "Chapter4/Proposition4.1.2"
number := false
%%%
**Proposition 4.1.2.** _If $`k[G]` is semisimple, then the characteristic of $`k` does not divide $`|G|`._

**Proof.** Write $`k[G] = \bigoplus_{i=1}^r \operatorname{End} V_i`, where the $`V_i` are irreducible representations and $`V_1 = k` is the trivial 1-dimensional representation. Then

$$`k[G] = k \oplus \bigoplus_{i=2}^r \operatorname{End} V_i = k \oplus \bigoplus_{i=2}^r d_i V_i,`
where $`d_i = \dim V_i`. By Schur's lemma,

$$`\operatorname{Hom}_{k[G]}(k, k[G]) = k\Lambda,`

$$`\operatorname{Hom}_{k[G]}(k[G], k) = k\epsilon,`

for nonzero homomorphisms of representations $`\epsilon : k[G] \to k` and $`\Lambda : k \to k[G]` unique up to scaling. We can take $`\epsilon` such that $`\epsilon(g) = 1` for all $`g \in G`, and we can take $`\Lambda` such that $`\Lambda(1) = \sum_{g \in G} g`. Then

$$`\epsilon \circ \Lambda(1) = \epsilon\left(\sum_{g \in G} g\right) = \sum_{g \in G} 1 = |G|.`

If $`|G| = 0`, then $`\Lambda` has no left inverse, as $`(a\epsilon) \circ \Lambda(1) = 0` for any $`a \in k`. This is a contradiction. $`\square`

## Formalization
%%%
tag := "Chapter4/Proposition4.1.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.FiniteGroup.RegularRepresentationDecomposition.FiniteGroup.exists_complete_simple_family_with_groupAlgebra_equiv}

{Manual.docstring RepresentationTheory.SemisimpleGroupAlgebraCardinality.isUnit_card_of_isSemisimpleRing}

### Supporting declarations

{Manual.docstring RepresentationTheory.FiniteGroup.RegularRepresentationDecomposition.FiniteGroup.exists_complete_simple_family_coordinateRepresentation}
