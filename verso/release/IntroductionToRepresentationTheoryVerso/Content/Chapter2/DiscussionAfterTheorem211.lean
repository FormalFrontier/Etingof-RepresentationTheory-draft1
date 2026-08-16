/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

set_option pp.rawOnError true

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.DiscussionAfterTheorem211

#doc (Manual) "Transition to quiver representation theory" =>
# Transition to quiver representation theory
%%%
tag := "Chapter2/Discussion_after_Theorem2.1.1"
number := false
%%%
As another example consider the representation theory of quivers. A **quiver** is an oriented graph $`Q` (which we will assume to be finite). A **representation** of $`Q` over a field $`k` is an assignment of a $`k`-vector space $`V_i` to every vertex $`i` of $`Q` and of a linear operator $`A_h : V_i \to V_j` to every directed edge $`h` going from $`i` to $`j` (loops and multiple edges are allowed). We will show that a representation of a quiver $`Q` is the same thing as a representation of a certain algebra $`P_Q` called the path algebra of $`Q`. Thus one may ask: what are the indecomposable finite dimensional representations of $`Q`?

More specifically, let us say that $`Q` is **of finite type** if it has finitely many indecomposable representations.

## Formalization
%%%
tag := "Chapter2/Discussion_after_Theorem2.1.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra.oppositeModuleRepresentationQuotientEquiv}

### Supporting declarations

{Manual.docstring RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.QuiverLinearDiagram}

{Manual.docstring RepresentationTheory.Foundations.TypeFamilies.TypeIndexedFamily}

{Manual.docstring RepresentationTheory.Quiver.FiniteTypeCriterion.FiniteQuiverRepresentation}

{Manual.docstring RepresentationTheory.Quiver.FiniteTypeCriterion.QuiverRepresentationFiniteness}

{Manual.docstring RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra.oppositeDirectSumAlgebraModule}

{Manual.docstring RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra.oppositeReconstructionLinearEquiv}

{Manual.docstring RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra.oppositeRepresentationOfModule}

{Manual.docstring RepresentationTheory.Quiver.PathAlgebra.Quiver.PathAlgebra.toModuleOppositeRepresentationEquiv}
