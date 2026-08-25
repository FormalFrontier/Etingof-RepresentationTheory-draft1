/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.DiscussionYoungProjectors

#doc (Manual) "Young projectors a\\_lambda, b\\_lambda, c\\_lambda and the Young symmetrizer" =>

# Young projectors a\_lambda, b\_lambda, c\_lambda and the Young symmetrizer
%%%
tag := "Chapter5/Discussion_Young_projectors"
number := false
%%%

Define the **Young projectors**

$$`a_\lambda := \frac{1}{|P_\lambda|} \sum_{g \in P_\lambda} g,`

$$`b_\lambda := \frac{1}{|Q_\lambda|} \sum_{g \in Q_\lambda} (-1)^g g,`

where $`(-1)^g` denotes the sign of the permutation $`g`. Set $`c_\lambda = a_\lambda b_\lambda`. Since $`P_\lambda \cap Q_\lambda = \{1\}`, this element is nonzero.

## Formalization
%%%
tag := "Chapter5/Discussion_Young_projectors/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.AuxiliarySubmodules.auxiliaryElement_ne_zero}

### Supporting declarations

{Manual.docstring RepresentationTheory.AuxiliarySubmodules.auxiliarySubmoduleLinearEquivIndexedSubmodule}

{Manual.docstring RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementD}

{Manual.docstring RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementE}

{Manual.docstring RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions.auxiliaryPartitionGroupAlgebraElementF}

{Manual.docstring RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra.left_idempotent_sq}

{Manual.docstring RepresentationTheory.SymmetricGroup.PartitionGroupAlgebra.right_idempotent_sq}
