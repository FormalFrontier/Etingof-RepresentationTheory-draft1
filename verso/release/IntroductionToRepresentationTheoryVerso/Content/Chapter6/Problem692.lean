/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter6.Problem692

#doc (Manual) "Problem 6.9.2: E8 lattice and root systems" =>

# Problem 6.9.2: E8 lattice and root systems
%%%
tag := "Chapter6/Problem6.9.2"
number := false
%%%

*Problem 6.9.2.* Let $`L \subset \frac{1}{2}\mathbb{Z}^8` be the lattice of vectors where the coordinates are either all integers or all half-integers (but not integers) and the sum of all coordinates is an even integer.

(a) Let $`\alpha_i = e_i - e_{i+1}`, $`i = 1, \ldots, 6`, $`\alpha_7 = e_6 + e_7`, $`\alpha_8 = -1/2 \sum_{i=1}^{8} e_i`. Show that $`\alpha_i` are a basis of $`L` (over $`\mathbb{Z}`).

(b) Show that roots in $`L` (under the usual inner product) form a root system of type $`E_8` (compute the inner products of $`\alpha_i`).

(c) Show that the $`E_7` and $`E_6` lattices can be obtained as the sets of vectors in the $`E_8` lattice $`L` where the first two, respectively three, coordinates (in the basis $`e_i`) are equal.

(d) Show that $`E_6`, $`E_7`, $`E_8` have 72, 126, and 240 roots, respectively (enumerate types of roots in terms of the presentations in the basis $`e_i`, and count the roots of each type).

## Formalization
%%%
tag := "Chapter6/Problem6.9.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.EightDimensionalRationalVectors.ncard_setTransform_rationalVectorSetA}

{Manual.docstring RepresentationTheory.EightDimensionalRationalVectors.ncard_setTransform_rationalVectorSetB}

{Manual.docstring RepresentationTheory.EightDimensionalRationalVectors.ncard_setTransform_rationalVectorSetC}

{Manual.docstring RepresentationTheory.RationalVectorRootSystems.eightRationalVectors_configuration}

### Supporting declarations

{Manual.docstring RepresentationTheory.EightDimensionalRationalVectors.Auxiliary.rationalVectorSetA}

{Manual.docstring RepresentationTheory.EightDimensionalRationalVectors.Auxiliary.rationalVectorSetB}

{Manual.docstring RepresentationTheory.EightDimensionalRationalVectors.rationalVectorSetC_integerSpan_characterization}

{Manual.docstring RepresentationTheory.RationalVectorRootSystems.eightVectorAuxiliarySet_isCrystallographicRootSet}

{Manual.docstring RepresentationTheory.RationalVectorRootSystems.sevenRationalVectors_integerPairingMatrix_eq_adjacency}

{Manual.docstring RepresentationTheory.RationalVectorRootSystems.sixRationalVectors_integerPairingMatrix_eq_adjacency}
