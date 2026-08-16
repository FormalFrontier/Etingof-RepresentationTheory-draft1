/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Example5123

#doc (Manual) "Specht modules for partitions (n), (1^n), and small n" =>

# Specht modules for partitions (n), (1^n), and small n
%%%
tag := "Chapter5/Example5.12.3"
number := false
%%%


**Example 5.12.3.** For the partition $`\lambda = (n)`, $`P_\lambda = S_n`, $`Q_\lambda = \{1\}`, so $`c_\lambda` is the symmetrizer, and hence $`V_\lambda` is the trivial representation.
For the partition $`\lambda = (1, \ldots, 1)`, $`Q_\lambda = S_n`, $`P_\lambda = \{1\}`, so $`c_\lambda` is the antisymmetrizer, and hence $`V_\lambda` is the sign representation.

$`n = 3`. For $`\lambda = (2, 1)`, $`V_\lambda = \mathbb{C}^2`.

$`n = 4`. For $`\lambda = (2, 2)`, $`V_\lambda = \mathbb{C}^2`; for $`\lambda = (3, 1)`, $`V_\lambda = \mathbb{C}^3_-`; for $`\lambda = (2, 1, 1)`, $`V_\lambda = \mathbb{C}^3_+`.

## Formalization
%%%
tag := "Chapter5/Example5.12.3/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.SymmetricGroup.PartitionSubspaceAuxiliary.finrank_partitionFourAuxiliaryTwo_eq_two}

{Manual.docstring RepresentationTheory.SymmetricGroup.PartitionSubspaceAuxiliary.finrank_partitionThreeAuxiliary_eq_two}

{Manual.docstring RepresentationTheory.SymmetricGroup.PartitionSubspaceAuxiliary.perm_smul_positivePartitionAuxiliaryAlt_eq_self}

{Manual.docstring RepresentationTheory.SymmetricGroup.PartitionSubspaceAuxiliary.perm_smul_positivePartitionAuxiliary_eq_sign_smul}

### Supporting declarations

{Manual.docstring RepresentationTheory.SymmetricGroup.PartitionSubspaceAuxiliary.nonempty_auxiliaryIso_partitionFourAuxiliaryOne}

{Manual.docstring RepresentationTheory.SymmetricGroup.PartitionSubspaceAuxiliary.nonempty_auxiliaryIso_partitionFourAuxiliaryThree}
