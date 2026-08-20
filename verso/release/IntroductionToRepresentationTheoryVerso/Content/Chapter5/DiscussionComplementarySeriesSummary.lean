/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.DiscussionComplementarySeriesSummary

#doc (Manual) "Summary: all q^2-1 irreducible representations of GL\\_2(F\\_q) found" =>

# Summary: all q^2-1 irreducible representations of GL\_2(F\_q) found
%%%
tag := "Chapter5/Discussion_complementary_series_summary"
number := false
%%%

We have now shown that for any $`\nu` with $`\nu^q \neq \nu` the representation $`Y_\nu` with the same character as

$$`W_1 \otimes V_{\alpha,1} - V_{\alpha,1} - \operatorname{Ind}_K^G \mathbb{C}_\nu`

exists and is irreducible. These characters are distinct for distinct pairs $`(\alpha, \nu)` (up to switching $`\nu \to \nu^q`), so there are $`\frac{q(q-1)}{2}` such representations, each of dimension $`q - 1`. These representations are called complementary series representations.

We have thus found $`q - 1` 1-dimensional representations of $`G`, $`\frac{q(q-1)}{2}` principal series representations, and $`\frac{q(q-1)}{2}` complementary series representations, for a total of $`q^2 - 1` representations, i.e., the number of conjugacy classes in $`G`. This implies that we have in fact found all irreducible representations of $`GL_2(\mathbb{F}_q)`.

## Formalization
%%%
tag := "Chapter5/Discussion_complementary_series_summary/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.FiniteGroups.GL2Conjugacy.card_conjClasses_eq_fieldCard_sq_sub_one}

{Manual.docstring RepresentationTheory.GeneralLinearGroupTwoIrreps.auxiliaryRepresentation}

{Manual.docstring RepresentationTheory.GeneralLinearGroupTwoIrreps.auxiliaryRepresentation_iso_injective}

{Manual.docstring RepresentationTheory.GeneralLinearGroupTwoIrreps.auxiliaryRepresentation_simple}

{Manual.docstring RepresentationTheory.GeneralLinearGroupTwoIrreps.card_auxiliaryIndexType}

{Manual.docstring RepresentationTheory.GeneralLinearGroupTwoIrreps.card_conjClasses_generalLinearGroup_two}

{Manual.docstring RepresentationTheory.GeneralLinearGroupTwoIrreps.eq_auxiliaryExpression_of_eq_card_conjClasses}

{Manual.docstring RepresentationTheory.GeneralLinearGroupTwoIrreps.existsUnique_auxiliaryRepresentation_iso}

{Manual.docstring RepresentationTheory.GeneralLinearGroupTwoIrreps.exists_auxiliaryType_card}

{Manual.docstring RepresentationTheory.GeneralLinearGroupTwoIrreps.exists_completeSimpleFamily_card}

{Manual.docstring RepresentationTheory.GeneralLinearGroupTwoIrreps.exists_groupAlgebra_matrixDecomposition}

{Manual.docstring RepresentationTheory.GeneralLinearGroupTwoIrreps.galoisField_hasAuxiliaryProperty}

{Manual.docstring RepresentationTheory.GeneralLinearGroupTwoIrreps.simple_isIso_of_complete_family}

{Manual.docstring RepresentationTheory.GeneralLinearGroupTwoIrreps.sub_one_add_twice_div_eq_sq_sub_one}
