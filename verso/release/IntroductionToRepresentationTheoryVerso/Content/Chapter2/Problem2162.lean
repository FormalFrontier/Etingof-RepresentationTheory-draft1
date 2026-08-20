/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Problem2162

#doc (Manual) "Irreducible representations of the 2d Lie algebra; Lie theorem in positive characteristic" =>
# Irreducible representations of the 2d Lie algebra; Lie theorem in positive characteristic
%%%
tag := "Chapter2/Problem2.16.2"
number := false
%%%
**Problem 2.16.2.** Classify irreducible finite dimensional representations of the two-dimensional Lie algebra with basis $`X, Y` and commutation relation $`[X, Y] = Y`. Consider the cases of zero and positive characteristic. Is the Lie theorem true in positive characteristic?

## Formalization
%%%
tag := "Chapter2/Problem2.16.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.LieAlgebra.ModularRepresentations.not_forall_irreducible_finrank_eq_one}

### Supporting declarations

{Manual.docstring RepresentationTheory.LieAlgebra.ModularRepresentations.AuxiliaryType}

{Manual.docstring RepresentationTheory.LieAlgebra.ModularRepresentations.AuxiliaryType_aux1}

{Manual.docstring RepresentationTheory.LieAlgebra.ModularRepresentations.bracket_eq}

{Manual.docstring RepresentationTheory.LieAlgebra.ModularRepresentations.existsUnique_equiv_oneDimensional}

{Manual.docstring RepresentationTheory.LieAlgebra.ModularRepresentations.finrank_eq_aux1}

{Manual.docstring RepresentationTheory.LieAlgebra.ModularRepresentations.irreducibleModule_equiv_classification}

{Manual.docstring RepresentationTheory.LieAlgebra.ModularRepresentations.irreducibleModule_equiv_classification_unique}

{Manual.docstring RepresentationTheory.LieAlgebra.ModularRepresentations.matrixLieSubalgebra}

{Manual.docstring RepresentationTheory.LieAlgebra.ModularRepresentations.matrixLieSubalgebra_isSolvable}

{Manual.docstring RepresentationTheory.LieAlgebra.ModularRepresentations.modularFamily_isIrreducible}

{Manual.docstring RepresentationTheory.LieAlgebra.ModularRepresentations.nonempty_lieModuleEquiv_iff}

{Manual.docstring RepresentationTheory.LieAlgebra.ModularRepresentations.not_nonempty_lieModuleEquiv_modular}
