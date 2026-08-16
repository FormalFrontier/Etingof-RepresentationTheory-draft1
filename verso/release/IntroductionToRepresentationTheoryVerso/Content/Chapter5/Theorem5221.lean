/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Theorem5221

#doc (Manual) "Weyl character formula: vanishing criterion, character of L\\_lambda, and dimension formula" =>

# Weyl character formula: vanishing criterion, character of L\_lambda, and dimension formula
%%%
tag := "Chapter5/Theorem5.22.1"
number := false
%%%

*Theorem 5.22.1* (Weyl character formula). _The representation $`L_\lambda` is zero if and only if $`N < p`, where $`p` is the number of parts of $`\lambda`. If $`N \geq p`, the character of $`L_\lambda` is the Schur polynomial $`S_\lambda(x)`. Therefore, the dimension of $`L_\lambda` is given by the formula_

$$`\dim L_\lambda = \prod_{1 \leq i < j \leq N} \frac{\lambda_i - \lambda_j + j - i}{j - i}.`

## Formalization
%%%
tag := "Chapter5/Theorem5.22.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.GeneralLinearGroup.WeightCharacter.finrank_schurRepresentation_eq}

{Manual.docstring RepresentationTheory.GeneralLinearGroup.WeightCharacter.weightCharacter_schurRepresentation_eq}

{Manual.docstring RepresentationTheory.Partitions.GeneralLinear.partitionIndexedRepresentation_associatedValue_eq_of_partitionLength_le_rank}

{Manual.docstring RepresentationTheory.Partitions.GeneralLinear.partitionIndexedRepresentation_finrank_cast_eq_associatedValue}

{Manual.docstring RepresentationTheory.Partitions.GeneralLinear.partitionIndexedSubmodule_eq_bot_iff_rank_lt_partitionLength}

{Manual.docstring RepresentationTheory.Partitions.GeneralLinear.partitionIndexedSubmodule_vanishing_and_representationFormulas}

{Manual.docstring RepresentationTheory.Partitions.GeneralLinear.selectedPartitionOfTwo_complexSubmodule_rank_one_eq_bot}

{Manual.docstring RepresentationTheory.Partitions.GeneralLinear.selectedPartitionOfTwo_complexSubmodule_rank_two_ne_bot}

### Supporting declarations

{Manual.docstring RepresentationTheory.Partitions.GeneralLinear.partitionIndexedRepresentation_finrank_eq_zero_iff_rank_lt_partitionLength}

{Manual.docstring RepresentationTheory.Partitions.GeneralLinear.partitionIndexedSubmodule_ne_bot_iff_partitionLength_le_rank}
