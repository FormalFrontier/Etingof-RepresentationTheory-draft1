/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Discussion1dimReps

#doc (Manual) "G/\\[G,G\\] \u2245 F\\_q^\u00d7 and description of 1-dimensional representations C\\_xi" =>

# G/\[G,G\] ≅ F\_q^× and description of 1-dimensional representations C\_xi
%%%
tag := "Chapter5/Discussion_1dim_reps"
number := false
%%%

Therefore,

$$`G/[G, G] \cong \mathbb{F}_q^\times \quad \text{via } g \mapsto \det(g).`

The 1-dimensional representations of $`G` thus have the form

$$`\rho(g) = \xi\bigl(\det(g)\bigr),`

where $`\xi` is a homomorphism

$$`\xi : \mathbb{F}_q^\times \to \mathbb{C}^\times;`

so there are $`q - 1` such representations, denoted $`\mathbb{C}_\xi`.

## Formalization
%%%
tag := "Chapter5/Discussion_1dim_reps/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.AuxiliaryTypeCharacters.card_auxiliaryType_complexCharacters}

{Manual.docstring RepresentationTheory.AuxiliaryTypeCharacters.unitsCharacterEquiv}

### Supporting declarations

{Manual.docstring RepresentationTheory.AuxiliaryTypeCharacters.unitsCharacterEquiv_apply}
