/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter4.Problem4121

#doc (Manual) "Irreducible representations of dihedral groups" =>

# Irreducible representations of dihedral groups
%%%
tag := "Chapter4/Problem4.12.1"
number := false
%%%

**Problem 4.12.1.** Let $`G` be the group of symmetries of a regular $`N`-gon (it has $`2N` elements).

(a) Describe all irreducible complex representations of this group (consider the cases of odd and even $`N`).

(b) Let $`V` be the 2-dimensional complex representation of $`G` obtained by complexification of the standard representation on the real plane (the plane of the polygon). Find the decomposition of $`V \otimes V` in a direct sum of irreducible representations.

## Formalization
%%%
tag := "Chapter4/Problem4.12.1/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.DihedralGroupComplexRepresentations.auxiliaryClassFunctionA}

{Manual.docstring RepresentationTheory.DihedralGroupComplexRepresentations.auxiliaryClassFunctionB}

{Manual.docstring RepresentationTheory.DihedralGroupComplexRepresentations.auxiliaryClassFunctionC}

{Manual.docstring RepresentationTheory.DihedralGroupComplexRepresentations.auxiliaryClassFunctionC_sq}

{Manual.docstring RepresentationTheory.DihedralGroupComplexRepresentations.auxiliaryDirectSumRepresentation}

{Manual.docstring RepresentationTheory.DihedralGroupComplexRepresentations.card_auxiliaryParameter_of_even}

{Manual.docstring RepresentationTheory.DihedralGroupComplexRepresentations.card_auxiliaryParameter_of_odd}

{Manual.docstring RepresentationTheory.DihedralGroupComplexRepresentations.card_linearCharacters_add_card_auxiliaryParameter_of_even}

{Manual.docstring RepresentationTheory.DihedralGroupComplexRepresentations.card_linearCharacters_add_card_auxiliaryParameter_of_odd}

{Manual.docstring RepresentationTheory.DihedralGroupComplexRepresentations.card_linearCharacters_add_four_mul_card_auxiliaryParameter}

{Manual.docstring RepresentationTheory.DihedralGroupComplexRepresentations.card_linearCharacters_of_even}

{Manual.docstring RepresentationTheory.DihedralGroupComplexRepresentations.card_linearCharacters_of_odd}

{Manual.docstring RepresentationTheory.DihedralGroupComplexRepresentations.finrank_eq_one_or_two_of_isSimpleModule}

{Manual.docstring RepresentationTheory.DihedralGroupComplexRepresentations.linearCharactersEquivUnitPairs}

{Manual.docstring RepresentationTheory.DihedralGroupComplexRepresentations.simpleRepresentation_iso_linear_or_twoDimensional}

{Manual.docstring RepresentationTheory.DihedralGroupComplexRepresentations.tensorSquare_twoDimensionalRepresentation_one_iso_auxiliaryDirectSum}

{Manual.docstring RepresentationTheory.DihedralGroupComplexRepresentations.twoDimensionalRepresentation}

{Manual.docstring RepresentationTheory.DihedralGroupComplexRepresentations.twoDimensionalRepresentation_isSimpleModule}

{Manual.docstring RepresentationTheory.DihedralGroupComplexRepresentations.twoDimensionalRepresentation_one_character}

{Manual.docstring RepresentationTheory.DihedralGroupComplexRepresentations.twoDimensionalRepresentation_two_character}

{Manual.docstring RepresentationTheory.DihedralGroupComplexRepresentations.twoDimensionalRepresentations_not_equivalent_of_trace_ne}
