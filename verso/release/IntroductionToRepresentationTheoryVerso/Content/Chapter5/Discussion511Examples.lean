/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Discussion511Examples

#doc (Manual) "Examples of induced representations for S\\_3 and S\\_4" =>

# Examples of induced representations for S\_3 and S\_4
%%%
tag := "Chapter5/Discussion_5.11_examples"
number := false
%%%

(1) Let $`G = S_3`, $`H = \mathbb{Z}_2`. Using the Frobenius reciprocity, we obtain $`\operatorname{Ind}_H^G \mathbb{C}_+ = \mathbb{C}^2 \oplus \mathbb{C}_+` and $`\operatorname{Ind}_H^G \mathbb{C}_- = \mathbb{C}^2 \oplus \mathbb{C}_-`.

(2) Let $`G = S_3`, $`H = \mathbb{Z}_3`. Then we obtain $`\operatorname{Ind}_H^G \mathbb{C}_+ = \mathbb{C}_+ \oplus \mathbb{C}_-`, $`\operatorname{Ind}_H^G \mathbb{C}_\epsilon = \operatorname{Ind}_H^G \mathbb{C}_{\epsilon^2} = \mathbb{C}^2`.

(3) Let $`G = S_4`, $`H = S_3`. Then $`\operatorname{Ind}_H^G \mathbb{C}_+ = \mathbb{C}_+ \oplus \mathbb{C}^3_-`, $`\operatorname{Ind}_H^G \mathbb{C}_- = \mathbb{C}_- \oplus \mathbb{C}^3_+`, $`\operatorname{Ind}_H^G \mathbb{C}^2 = \mathbb{C}^2 \oplus \mathbb{C}^3_- \oplus \mathbb{C}^3_+`.

## Formalization
%%%
tag := "Chapter5/Discussion_5.11_examples/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.AuxiliaryRepresentationComputations.induced_auxiliaryCharacterOne_iso_auxiliaryRepresentation}

{Manual.docstring RepresentationTheory.AuxiliaryRepresentationComputations.induced_auxiliaryCharacterTwo_iso_auxiliaryRepresentation}

{Manual.docstring RepresentationTheory.AuxiliaryRepresentationComputations.induced_restrictedCharacter_iso_biprod}

{Manual.docstring RepresentationTheory.AuxiliaryRepresentationComputations.induced_trivial_auxiliarySubgroupA_iso_biprod}

{Manual.docstring RepresentationTheory.AuxiliaryRepresentationComputations.induced_trivial_auxiliarySubgroupB_iso_biprod}

{Manual.docstring RepresentationTheory.FiniteGroupRepresentations.SubgroupInductionAuxiliary.induced_auxiliary_sign_iso_biprod}

{Manual.docstring RepresentationTheory.FiniteGroupRepresentations.SubgroupInductionAuxiliary.induced_auxiliary_subrepresentation_iso_biprod}

{Manual.docstring RepresentationTheory.FiniteGroupRepresentations.SubgroupInductionAuxiliary.induced_auxiliary_trivial_iso_biprod}
