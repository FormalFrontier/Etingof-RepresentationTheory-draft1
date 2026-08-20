/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter4.Example491

@[role]
meta def emptyTableCell : Verso.Doc.Elab.RoleExpanderOf Unit
  | (), _ => ``(Verso.Doc.Inline.empty)

#doc (Manual) "Tensor product multiplicities for S\\_3, S\\_4, and A\\_5" =>

# Tensor product multiplicities for S\_3, S\_4, and A\_5
%%%
tag := "Chapter4/Example4.9.1"
number := false
%%%

*Example 4.9.1.* The following tables represent computed tensor product multiplicities of irreducible representations of $`S_3`, $`S_4`, and $`A_5`, respectively:

:::table +header
*
  * $`S_3`
  * $`\mathbb{C}_+`
  * $`\mathbb{C}_-`
  * $`\mathbb{C}^2`
*
  * $`\mathbb{C}_+`
  * $`\mathbb{C}_+`
  * $`\mathbb{C}_-`
  * $`\mathbb{C}^2`
*
  * $`\mathbb{C}_-`
  * {emptyTableCell}`_`
  * $`\mathbb{C}_+`
  * $`\mathbb{C}^2`
*
  * $`\mathbb{C}^2`
  * {emptyTableCell}`_`
  * {emptyTableCell}`_`
  * $`\mathbb{C}_+ \oplus \mathbb{C}_- \oplus \mathbb{C}^2`
:::

:::table +header
*
  * $`S_4`
  * $`\mathbb{C}_+`
  * $`\mathbb{C}_-`
  * $`\mathbb{C}^2`
  * $`\mathbb{C}^3_+`
  * $`\mathbb{C}^3_-`
*
  * $`\mathbb{C}_+`
  * $`\mathbb{C}_+`
  * $`\mathbb{C}_-`
  * $`\mathbb{C}^2`
  * $`\mathbb{C}^3_+`
  * $`\mathbb{C}^3_-`
*
  * $`\mathbb{C}_-`
  * {emptyTableCell}`_`
  * $`\mathbb{C}_+`
  * $`\mathbb{C}^2`
  * $`\mathbb{C}^3_-`
  * $`\mathbb{C}^3_+`
*
  * $`\mathbb{C}^2`
  * {emptyTableCell}`_`
  * {emptyTableCell}`_`
  * $`\mathbb{C}_+ \oplus \mathbb{C}_- \oplus \mathbb{C}^2`
  * $`\mathbb{C}^3_+ \oplus \mathbb{C}^3_-`
  * $`\mathbb{C}^3_+ \oplus \mathbb{C}^3_-`
*
  * $`\mathbb{C}^3_+`
  * {emptyTableCell}`_`
  * {emptyTableCell}`_`
  * {emptyTableCell}`_`
  * $`\mathbb{C}_+ \oplus \mathbb{C}^2 \oplus \mathbb{C}^3_+ \oplus \mathbb{C}^3_-`
  * $`\mathbb{C}_- \oplus \mathbb{C}^2 \oplus \mathbb{C}^3_+ \oplus \mathbb{C}^3_-`
*
  * $`\mathbb{C}^3_-`
  * {emptyTableCell}`_`
  * {emptyTableCell}`_`
  * {emptyTableCell}`_`
  * {emptyTableCell}`_`
  * $`\mathbb{C}_+ \oplus \mathbb{C}^2 \oplus \mathbb{C}^3_+ \oplus \mathbb{C}^3_-`
:::

:::table +header
*
  * $`A_5`
  * $`\mathbb{C}`
  * $`\mathbb{C}^3_+`
  * $`\mathbb{C}^3_-`
  * $`\mathbb{C}^4`
  * $`\mathbb{C}^5`
*
  * $`\mathbb{C}`
  * $`\mathbb{C}`
  * $`\mathbb{C}^3_+`
  * $`\mathbb{C}^3_-`
  * $`\mathbb{C}^4`
  * $`\mathbb{C}^5`
*
  * $`\mathbb{C}^3_+`
  * {emptyTableCell}`_`
  * $`\mathbb{C} \oplus \mathbb{C}^5 \oplus \mathbb{C}^3_+`
  * $`\mathbb{C}^4 \oplus \mathbb{C}^5`
  * $`\mathbb{C}^3_- \oplus \mathbb{C}^4 \oplus \mathbb{C}^5`
  * $`\mathbb{C}^3_+ \oplus \mathbb{C}^3_- \oplus \mathbb{C}^4 \oplus \mathbb{C}^5`
*
  * $`\mathbb{C}^3_-`
  * {emptyTableCell}`_`
  * {emptyTableCell}`_`
  * $`\mathbb{C} \oplus \mathbb{C}^5 \oplus \mathbb{C}^3_-`
  * $`\mathbb{C}^3_+ \oplus \mathbb{C}^4 \oplus \mathbb{C}^5`
  * $`\mathbb{C}^3_+ \oplus \mathbb{C}^3_- \oplus \mathbb{C}^4 \oplus \mathbb{C}^5`
*
  * $`\mathbb{C}^4`
  * {emptyTableCell}`_`
  * {emptyTableCell}`_`
  * {emptyTableCell}`_`
  * $`\mathbb{C}^3_+ \oplus \mathbb{C}^3_- \oplus \mathbb{C} \oplus \mathbb{C}^4 \oplus \mathbb{C}^5`
  * $`\mathbb{C}^3_+ \oplus \mathbb{C}^3_- \oplus 2\mathbb{C}^5 \oplus \mathbb{C}^4`
*
  * $`\mathbb{C}^5`
  * {emptyTableCell}`_`
  * {emptyTableCell}`_`
  * {emptyTableCell}`_`
  * {emptyTableCell}`_`
  * $`\mathbb{C} \oplus \mathbb{C}^3_+ \oplus \mathbb{C}^3_- \oplus 2\mathbb{C}^4 \oplus 2\mathbb{C}^5`
:::

## Formalization
%%%
tag := "Chapter4/Example4.9.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.RepresentationTensorDecompositions.secondFiveRepresentationFamily_tensor_iso_multiplicitySum}

### Supporting declarations

{Manual.docstring RepresentationTheory.RepresentationTensorDecompositions.firstFiveRepresentationFamily_tensor_iso_biproduct}

{Manual.docstring RepresentationTheory.RepresentationTensorDecompositions.firstFiveRepresentationFamily_tensor_iso_multiplicitySum}

{Manual.docstring RepresentationTheory.RepresentationTensorDecompositions.reducedPermutationRepresentation_tensor_sq_iso}

{Manual.docstring RepresentationTheory.RepresentationTensorDecompositions.representationFamily_tensor_iso_biproduct}

{Manual.docstring RepresentationTheory.RepresentationTensorDecompositions.representationFamily_tensor_iso_multiplicitySum}

{Manual.docstring RepresentationTheory.RepresentationTensorDecompositions.secondFiveRepresentationFamily_tensor_iso_biproduct}
