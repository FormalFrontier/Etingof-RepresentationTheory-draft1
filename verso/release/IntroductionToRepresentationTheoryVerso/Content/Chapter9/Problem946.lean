/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter9.Problem946

#doc (Manual) "Homological dimension and Cartan matrix of path algebras" =>

# Homological dimension and Cartan matrix of path algebras
%%%
tag := "Chapter9/Problem9.4.6"
number := false
%%%

*Problem 9.4.6.* (i) Show that the path algebra $`P_Q` of any quiver $`Q` with at least one edge has homological dimension 1. In particular, the homological dimension of the free algebra $`k\langle x_1, \ldots, x_n \rangle` is 1 (for $`n \geq 1`).

(ii) Let $`Q` be a finite oriented graph without oriented cycles. Find the Cartan matrix of its path algebra $`P_Q`.

## Formalization
%%%
tag := "Chapter9/Problem9.4.6/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Quiver.PathAlgebra.LoopQuiver.freeAlgebra_associatedValue_eq_one}

{Manual.docstring RepresentationTheory.Quiver.PathAlgebra.LoopQuiver.quiverAssociatedAlgebra_associatedValue_eq_one_of_exists_arrow}

### Supporting declarations

{Manual.docstring RepresentationTheory.Quiver.PathAlgebra.LoopQuiver.associatedMatrix_eq_quiverNatMatrix_of_pathIndexedLinearEquiv}

{Manual.docstring RepresentationTheory.Quiver.PathAlgebra.LoopQuiver.freeAlgebraEquivLoopQuiverAssociatedAlgebra}

{Manual.docstring RepresentationTheory.Quiver.PathAlgebra.LoopQuiver.quiverAssociatedAlgebra_condition_at_one}
