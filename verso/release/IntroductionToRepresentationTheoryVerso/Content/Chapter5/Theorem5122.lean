/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Theorem5122

#doc (Manual) "Classification of irreducible representations of S\\_n via Specht modules V\\_lambda" =>

# Classification of irreducible representations of S\_n via Specht modules V\_lambda
%%%
tag := "Chapter5/Theorem5.12.2"
number := false
%%%

The irreducible representations of $`S_n` are described by the following theorem.

**Theorem 5.12.2.** _The subspace $`V_\lambda := \mathbb{C}[S_n] c_\lambda` of $`\mathbb{C}[S_n]` is an irreducible representation of $`S_n` under left multiplication. Every irreducible representation of $`S_n` is isomorphic to $`V_\lambda` for a unique $`\lambda`._

The modules $`V_\lambda` are called the **Specht modules**.

The proof of this theorem is given in the next subsection.

## Formalization
%%%
tag := "Chapter5/Theorem5.12.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.PartitionLinearEquivBoundsAndMonoidAlgebra.isEmpty_linearEquiv_of_ne_partition}

### Supporting declarations

{Manual.docstring RepresentationTheory.PartitionAuxiliary.partitionSubmodule_isSimpleModule}

{Manual.docstring RepresentationTheory.SimpleModule.SubtypeRepresentation.exists_linearEquiv_to_subtype}
