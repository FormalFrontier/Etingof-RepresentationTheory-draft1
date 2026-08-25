/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso Genre

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.DiscussionCommutativityExamples

#doc (Manual) "Commutativity of the examples in 2.2.4" =>
# Commutativity of the examples in 2.2.4
%%%
tag := "Chapter2/Discussion_commutativity_examples"
number := false
%%%
For instance, in the above examples, $`A` is commutative in cases 1 and 2 but not commutative in cases 3 (if $`\dim V > 1`) and 4 (if $`n > 1`). In case 5, $`A` is commutative if and only if $`G` is commutative.

## Formalization
%%%
tag := "Chapter2/Discussion_commutativity_examples/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Noncommutativity.exists_noncommuting_pair_of_two_le_rank}

{Manual.docstring RepresentationTheory.Algebra.Noncommutativity.monoidAlgebra_mul_comm_iff}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.Noncommutativity.exists_noncommuting_pair_of_one_lt}
