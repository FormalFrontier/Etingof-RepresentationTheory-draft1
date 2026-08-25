/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso Genre

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.DiscussionIrreducibleVsIndecomposable

#doc (Manual) "Irreducible implies indecomposable; main problems of representation theory" =>
# Irreducible implies indecomposable; main problems of representation theory
%%%
tag := "Chapter2/Discussion_irreducible_vs_indecomposable"
number := false
%%%
It is obvious that an irreducible representation is indecomposable. On the other hand, we will see below that the converse statement is false in general.

One of the main problems of representation theory is to classify irreducible and indecomposable representations of a given algebra up to isomorphism. This problem is usually hard and often can be solved only partially (say, for finite dimensional representations). Below we will see a number of examples in which this problem is partially or fully solved for specific algebras.

## Formalization
%%%
tag := "Chapter2/Discussion_irreducible_vs_indecomposable/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate.of_isSimpleModule}

### Supporting declarations

{Manual.docstring RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.isIndecomposableModule_and_not_isSimpleModule_jordanBlock_two}
