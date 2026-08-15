/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter4.Problem4122

#doc (Manual) "Representations of the Heisenberg group" =>

# Representations of the Heisenberg group
%%%
tag := "Chapter4/Problem4.12.2"
number := false
%%%

**Problem 4.12.2.** Let $`p` be a prime. Let $`G` be the group of $`3 \times 3` matrices over $`\mathbb{F}_p` which are upper triangular and have 1's on the diagonal, under multiplication (its order is $`p^3`). It is called the **Heisenberg group**. For any complex number $`z` such that $`z^p = 1`, we define a representation of $`G` on the space $`V` of complex functions on $`\mathbb{F}_p` by

$$`(\rho \begin{pmatrix} 1 & 1 & 0 \\ 0 & 1 & 0 \\ 0 & 0 & 1 \end{pmatrix} f)(x) = f(x - 1),`
$$`(\rho \begin{pmatrix} 1 & 0 & 0 \\ 0 & 1 & 1 \\ 0 & 0 & 1 \end{pmatrix} f)(x) = z^x f(x)`

(note that $`z^x` makes sense since $`z^p = 1`).

(a) Show that such a representation exists and is unique, and compute $`\rho(g)` for all $`g \in G`.

(b) Denote this representation by $`R_z`. Show that $`R_z` is irreducible if and only if $`z \neq 1`.

(c) Classify all 1-dimensional representations of $`G`. Show that $`R_1` decomposes into a direct sum of 1-dimensional representations, where each of them occurs exactly once.

(d) Use (a)—(c) and the "sum of squares" formula to classify all irreducible representations of $`G`.

## Formalization
%%%
tag := "Chapter4/Problem4.12.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.ThreeCoordinateGroupRepresentations.characterPrecompositionEquiv}

{Manual.docstring RepresentationTheory.ThreeCoordinateGroupRepresentations.character_iso_iff}

{Manual.docstring RepresentationTheory.ThreeCoordinateGroupRepresentations.character_representation_not_iso_auxiliary}

{Manual.docstring RepresentationTheory.ThreeCoordinateGroupRepresentations.existsUnique_shift_scale_representation}

{Manual.docstring RepresentationTheory.ThreeCoordinateGroupRepresentations.exists_invariant_line_decomposition}

{Manual.docstring RepresentationTheory.ThreeCoordinateGroupRepresentations.shiftScaleAction_apply}

{Manual.docstring RepresentationTheory.ThreeCoordinateGroupRepresentations.shiftScaleRepresentation_iso_iff}

{Manual.docstring RepresentationTheory.ThreeCoordinateGroupRepresentations.shiftScaleRepresentation_simple_iff}

{Manual.docstring RepresentationTheory.ThreeCoordinateGroupRepresentations.simple_representation_iso_character_or_shiftScale}

### Supporting declarations

{Manual.docstring RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup.card_eq_cube}

{Manual.docstring RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup.closure_generators_eq_top}

{Manual.docstring RepresentationTheory.ThreeCoordinateGroupRepresentations.ThreeCoordinateGroup.normalForm}

{Manual.docstring RepresentationTheory.ThreeCoordinateGroupRepresentations.card_eq_character_count}

{Manual.docstring RepresentationTheory.ThreeCoordinateGroupRepresentations.characterPrecompositionEquiv_apply}

{Manual.docstring RepresentationTheory.ThreeCoordinateGroupRepresentations.characterType_card}

{Manual.docstring RepresentationTheory.ThreeCoordinateGroupRepresentations.characterType_nonempty_equiv_auxiliary}

{Manual.docstring RepresentationTheory.ThreeCoordinateGroupRepresentations.character_card_eq_square}

{Manual.docstring RepresentationTheory.ThreeCoordinateGroupRepresentations.coordinateQuotientHom}

{Manual.docstring RepresentationTheory.ThreeCoordinateGroupRepresentations.coordinateQuotientHom_surjective}

{Manual.docstring RepresentationTheory.ThreeCoordinateGroupRepresentations.ker_coordinateQuotient_le_ker}

{Manual.docstring RepresentationTheory.ThreeCoordinateGroupRepresentations.nontrivialRoots_card}

{Manual.docstring RepresentationTheory.ThreeCoordinateGroupRepresentations.shiftScaleRepresentation}

{Manual.docstring RepresentationTheory.ThreeCoordinateGroupRepresentations.shiftScaleRepresentation_firstGenerator_apply}

{Manual.docstring RepresentationTheory.ThreeCoordinateGroupRepresentations.shiftScaleRepresentation_secondGenerator_apply}

{Manual.docstring RepresentationTheory.ThreeCoordinateGroupRepresentations.simple_representation_finrank_eq_one_or_index}
