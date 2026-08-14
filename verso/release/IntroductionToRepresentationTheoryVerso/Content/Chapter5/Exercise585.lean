/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Exercise585

#doc (Manual) "Induced representation via idempotent e\\_chi" =>

# Induced representation via idempotent e\_chi
%%%
tag := "Chapter5/Exercise5.8.5"
number := false
%%%

**Exercise 5.8.5.** Let $`K \subset G` be finite groups, and let $`\chi : K \to \mathbb{C}^*` be a homomorphism. Let $`\mathbb{C}_\chi` be the corresponding 1-dimensional representation of $`K`. Let

$$`e_\chi = \frac{1}{|K|} \sum_{g \in K} \chi(g)^{-1} g \in \mathbb{C}[K]`

be the idempotent corresponding to $`\chi`. Show that the $`G`-representation $`\operatorname{Ind}_K^G \mathbb{C}_\chi` is naturally isomorphic to $`\mathbb{C}[G] e_\chi` (with $`G` acting by left multiplication).

## Formalization
%%%
tag := "Chapter5/Exercise5.8.5/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.SubgroupCharacters.auxiliary_equivariant_map_of_subgroup_character}

{Manual.docstring RepresentationTheory.SubgroupCharacters.groupAlgebraElementOfSubgroupCharacter}

{Manual.docstring RepresentationTheory.SubgroupCharacters.representationOfSubgroupCharacter}

{Manual.docstring RepresentationTheory.SubgroupCharacters.submoduleOfSubgroupCharacter}
