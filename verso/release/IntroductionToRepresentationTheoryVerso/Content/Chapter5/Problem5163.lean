/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Problem5163

#doc (Manual) "Diagonalizability of (12)+...+(1n) and rectangular Young diagrams" =>

# Diagonalizability of (12)+...+(1n) and rectangular Young diagrams
%%%
tag := "Chapter5/Problem5.16.3"
number := false
%%%

*Problem 5.16.3.* (a) Let $`V` be any finite dimensional representation of $`S_n`. Show that the element $`E := (12) + \cdots + (1n)` is diagonalizable and has integer eigenvalues on $`V` which are between $`1 - n` and $`n - 1`.

Hint: Represent $`E` as $`C_n - C_{n-1}`, where $`C_n = C` is the element from Problem 5.16.2.

(b) Show that the element $`(12) + \cdots + (1n)` acts on $`V_\lambda` by a scalar if and only if $`\lambda` is a rectangular Young diagram, and compute this scalar.

## Formalization
%%%
tag := "Chapter5/Problem5.16.3/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.PermutationPartitionActions.auxiliaryDegreeElementForPartitionPredicate_eigenvalue_is_integer}

{Manual.docstring RepresentationTheory.PermutationPartitionActions.auxiliaryDegreeElementForPartitionPredicate_exists_indexed_scalar_actions_and_eigenvalue_bounds}

{Manual.docstring RepresentationTheory.PermutationPartitionActions.auxiliaryDegreeElementForPartitionPredicate_scalarAction_iff_auxiliaryPartitionPredicate}

{Manual.docstring RepresentationTheory.PermutationPartitionActions.auxiliaryDegreeElementForPartitionPredicate_scalarAction_of_parts_eq_replicate}

### Supporting declarations

{Manual.docstring RepresentationTheory.PermutationPartitionActions.auxiliaryDegreeElementForPartitionPredicate}

{Manual.docstring RepresentationTheory.PermutationPartitionActions.auxiliaryDegreeElementForPartitionPredicate_eq_difference_of_displayedElements}

{Manual.docstring RepresentationTheory.PermutationPartitionActions.auxiliaryDegreeElement_scalarAction_iff_constant_integerPartitionValue}

{Manual.docstring RepresentationTheory.PermutationPartitionActions.exists_constant_partitionStatistic_iff_auxiliaryPartitionPredicate}
