/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.DiscussionLexicographicOrdering

#doc (Manual) "Definition of lexicographic ordering on partitions" =>

# Definition of lexicographic ordering on partitions
%%%
tag := "Chapter5/Discussion_lexicographic_ordering"
number := false
%%%

Let us introduce the *lexicographic ordering* on partitions: $`\lambda > \mu` if the first nonvanishing $`\lambda_i - \mu_i` is positive.

## Formalization
%%%
tag := "Chapter5/Discussion_lexicographic_ordering/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.SymmetricGroup.PartitionDominance.Partition.Dominates.lexLe}

{Manual.docstring RepresentationTheory.SymmetricGroup.PartitionDominance.Partition.LexLt.not_dominates}

### Supporting declarations

{Manual.docstring RepresentationTheory.SymmetricGroup.PartitionDominance.Partition.LexLe}

{Manual.docstring RepresentationTheory.SymmetricGroup.PartitionDominance.Partition.LexLt}

{Manual.docstring RepresentationTheory.SymmetricGroup.PartitionDominance.Partition.exists_lexLt}
