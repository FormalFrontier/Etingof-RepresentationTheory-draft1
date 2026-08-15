/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Introduction515

#doc (Manual) "Section 5.15: The Frobenius character formula" =>

# Section 5.15: The Frobenius character formula
%%%
tag := "Chapter5/Introduction_5.15"
number := false
%%%

## 5.15. The Frobenius character formula
%%%
tag := "Chapter5/Introduction_5.15/heading-1"
%%%

Let $`\Delta(x) = \prod_{1 \leq i < j \leq N} (x_i - x_j)`. Recall that $`\Delta(x)` is the Vandermonde determinant, $`\det(x_i^{N-j})`. Let $`\rho = (N-1, N-2, \ldots, 0) \in \mathbb{C}^N`. The following theorem, due to Frobenius, gives a character formula for the Specht modules $`V_\lambda`.

## Formalization
%%%
tag := "Chapter5/Introduction_5.15/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryFinsupp}

{Manual.docstring RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliaryPolynomial}

### Supporting declarations

{Manual.docstring RepresentationTheory.PartitionPolynomials.partitionExponentVector}
