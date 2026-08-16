/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.DiscussionAfterTheorem5221

#doc (Manual) "Irreducible representations of GL(V) labeled by Young diagrams" =>

# Irreducible representations of GL(V) labeled by Young diagrams
%%%
tag := "Chapter5/Discussion_after_Theorem5.22.1"
number := false
%%%

This shows that irreducible representations of $`GL(V)` which occur in $`V^{\otimes n}` for some $`n` are labeled by Young diagrams with any number of squares but at most $`N = \dim V` rows.

## Formalization
%%%
tag := "Chapter5/Discussion_after_Theorem5.22.1/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.PartitionedDecomposition.existsIndexedSimpleDecomposition}

{Manual.docstring RepresentationTheory.Partitions.GeneralLinear.partitionIndexedSubmodule_vanishing_and_representationFormulas}
