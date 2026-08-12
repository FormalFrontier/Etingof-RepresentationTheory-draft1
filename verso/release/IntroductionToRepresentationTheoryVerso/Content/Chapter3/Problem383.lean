/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.Problem383

#doc (Manual) "Krull-Schmidt theorem without algebraic closure" =>

# Krull-Schmidt theorem without algebraic closure
%%%
tag := "Chapter3/Problem3.8.3"
number := false
%%%
**Problem 3.8.3.** The above proof of Lemma 3.8.2 uses the condition that $`k` is an algebraically closed field. Prove Lemma 3.8.2 (and hence the Krull-Schmidt theorem) without this condition.

## Formalization
%%%
tag := "Chapter3/Problem3.8.3/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Module.FiniteDecompositions.bijective_or_nilpotent}

{Manual.docstring RepresentationTheory.Algebra.Module.FiniteDecompositions.exists_internal_family}

{Manual.docstring RepresentationTheory.Algebra.Module.FiniteDecompositions.internal_family_unique_up_to_permutation}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.Module.FiniteDecompositions.sum_nilpotent}
