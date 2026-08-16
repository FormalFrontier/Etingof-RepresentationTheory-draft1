/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Example513

#doc (Manual) "Types of irreducible representations of Z/nZ, S\\_3, S\\_4, A\\_5, Q\\_8" =>

# Types of irreducible representations of Z/nZ, S\_3, S\_4, A\_5, Q\_8
%%%
tag := "Chapter5/Example5.1.3"
number := false
%%%
**Example 5.1.3.** For $`\mathbb{Z}/n\mathbb{Z}` all irreducible representations are of complex type except the trivial one and, if $`n` is even, the "sign" representation, $`m \to (-1)^m`, which are of real type. For $`S_3` all three irreducible representations $`\mathbb{C}_+, \mathbb{C}_-, \mathbb{C}^2` are of real type. For $`S_4` there are five irreducible representations $`\mathbb{C}_+, \mathbb{C}_-, \mathbb{C}^2, \mathbb{C}^3_+, \mathbb{C}^3_-`, which are all of real type. Similarly, all five irreducible representations of $`A_5` — $`\mathbb{C}`, $`\mathbb{C}^3_+`, $`\mathbb{C}^3_-`, $`\mathbb{C}^4`, $`\mathbb{C}^5` — are of real type. As for $`Q_8`, its 1-dimensional representations are of real type, and the 2-dimensional one is of quaternionic type.

## Formalization
%%%
tag := "Chapter5/Example5.1.3/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.FiniteGroupRepresentationExamples.auxiliaryCharacterCriterionForFiniteCyclicGroup}

{Manual.docstring RepresentationTheory.FiniteGroupRepresentationExamples.auxiliaryCharacterCriterion_eq_one_or_eq_specifiedEvenOrder}

{Manual.docstring RepresentationTheory.FiniteGroupRepresentationExamples.auxiliaryPropertyForQuaternionRepresentationOnComplex}

{Manual.docstring RepresentationTheory.FiniteGroupRepresentationExamples.auxiliaryPropertyOfSimpleAlternatingFiveRepresentation}

{Manual.docstring RepresentationTheory.FiniteGroupRepresentationExamples.auxiliaryPropertyOfSimpleSymmetricFourRepresentation}

{Manual.docstring RepresentationTheory.FiniteGroupRepresentationExamples.auxiliaryPropertyOfSimpleSymmetricThreeRepresentation}

{Manual.docstring RepresentationTheory.FiniteGroupRepresentationExamples.simpleFiniteCyclicRepresentationIsoAuxiliary}

{Manual.docstring RepresentationTheory.FiniteGroupRepresentationExamples.simpleQuaternionRepresentationOfFinrankTwoIso}

### Supporting declarations

{Manual.docstring RepresentationTheory.FiniteGroupRepresentationExamples.existsSimpleQuaternionRepresentationWithAuxiliaryProperty}
