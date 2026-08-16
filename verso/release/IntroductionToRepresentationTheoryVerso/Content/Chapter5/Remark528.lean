/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Remark528

#doc (Manual) "Modification of vanishing argument without part (a)" =>

# Modification of vanishing argument without part (a)
%%%
tag := "Chapter5/Remark5.2.8"
number := false
%%%
**Remark 5.2.8.** Here is a modification of this argument, which does not use (a). Let $`N = |G|`. For any $`0 < j < N` coprime to $`N`, show that the map $`g \mapsto g^j` is a bijection $`G \to G`. Deduce that $`\prod_{g \neq 1} |\chi_V(g^j)|^2 = \beta`. Then show that $`\beta \in K := \mathbb{Q}(\zeta)`, $`\zeta = e^{2\pi i/N}`, and that it does not change under the automorphism of $`K` given by $`\zeta \mapsto \zeta^j`. Deduce that $`\beta` is an integer, and derive a contradiction.

## Formalization
%%%
tag := "Chapter5/Remark5.2.8/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.FiniteGroup.CharacterArithmetic.character_pairing_product_not_rat_between_zero_one}

{Manual.docstring RepresentationTheory.FiniteGroup.CharacterArithmetic.pow_bijective_of_card_coprime}

{Manual.docstring RepresentationTheory.FiniteGroup.CharacterArithmetic.prod_nonidentity_comp_pow_eq}

### Supporting declarations

{Manual.docstring RepresentationTheory.FiniteGroup.CharacterArithmetic.character_eq_sum_of_card_roots}

{Manual.docstring RepresentationTheory.FiniteGroup.CharacterArithmetic.character_normSq_product_isIntegral}

{Manual.docstring RepresentationTheory.FiniteGroup.CharacterArithmetic.character_pairing_product_is_rat}

{Manual.docstring RepresentationTheory.FiniteGroup.CharacterArithmetic.map_character_eq_character_pow}

{Manual.docstring RepresentationTheory.FiniteGroup.CharacterArithmetic.map_character_pairing_product_eq_of_card_coprime}

{Manual.docstring RepresentationTheory.FiniteGroup.CharacterArithmetic.rat_not_between_zero_one_of_complex_isIntegral}
