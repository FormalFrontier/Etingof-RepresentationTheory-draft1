/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Definition514

#doc (Manual) "Frobenius-Schur indicator" =>

# Frobenius-Schur indicator
%%%
tag := "Chapter5/Definition5.1.4"
number := false
%%%
**Definition 5.1.4.** The **Frobenius-Schur indicator** $`FS(V)` of an irreducible representation $`V` is $`0` if it is of complex type, $`1` if it is of real type, and $`-1` if it is of quaternionic type.

## Formalization
%%%
tag := "Chapter5/Definition5.1.4/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Representation.Character.AuxiliaryProperties.auxiliaryPredicate_iff_auxiliaryValue_eq_one}

{Manual.docstring RepresentationTheory.Representation.Character.AuxiliaryProperties.auxiliaryPredicate_iff_auxiliaryValue_eq_zero}

### Supporting declarations

{Manual.docstring RepresentationTheory.FiniteGroupRepresentations.AuxiliaryScalar.auxiliaryRepresentationScalar}

{Manual.docstring RepresentationTheory.Representation.Character.AuxiliaryProperties.auxiliaryStatement'''}
