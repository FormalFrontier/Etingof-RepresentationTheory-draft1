/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Remark5155

#doc (Manual) "Partial order on partitions and vanishing of Kostka numbers" =>

# Partial order on partitions and vanishing of Kostka numbers
%%%
tag := "Chapter5/Remark5.15.5"
number := false
%%%

*Remark 5.15.5.* For partitions $`\lambda` and $`\mu` of $`n`, let us say that $`\lambda \preceq \mu` or $`\mu \succeq \lambda` if $`\mu - \lambda` is a sum of vectors of the form $`e_i - e_j`, $`i < j` (called positive roots). This is a partial order, and $`\mu \succeq \lambda` implies $`\mu \geq \lambda`. It follows from Theorem 5.15.1 and its proof that

$$`\chi_\lambda = \sum_{\mu \succeq \lambda} \widetilde{K}_{\mu\lambda} \chi_{U_\mu},`

where $`(\widetilde{K}_{\lambda\mu})` is the matrix inverse to the matrix of Kostka numbers $`(K_{\lambda\mu})`. This implies that the Kostka numbers $`K_{\mu\lambda}` vanish unless $`\mu \succeq \lambda`.

## Formalization
%%%
tag := "Chapter5/Remark5.15.5/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Combinatorics.Partition.RootOrderMatrices.Partition.auxiliaryValue_eq_rootLe_matrix_sum}

{Manual.docstring RepresentationTheory.Combinatorics.Partition.RootOrderMatrices.Partition.rootOrder_iff_auxiliaryRelation}

{Manual.docstring RepresentationTheory.Combinatorics.Partition.RootOrderMatrices.Partition.rootOrder_isPartialOrder}

### Supporting declarations

{Manual.docstring RepresentationTheory.AuxiliaryPartitionLinearIndependentFamily.auxiliary_nat_values_eq}

{Manual.docstring RepresentationTheory.Combinatorics.Partition.RootOrderMatrices.Partition.auxiliaryCount_eq_zero_of_not_rootLe}

{Manual.docstring RepresentationTheory.Combinatorics.Partition.RootOrderMatrices.Partition.auxiliaryInverseMatrix_apply_eq_zero_of_not_rootLe}
