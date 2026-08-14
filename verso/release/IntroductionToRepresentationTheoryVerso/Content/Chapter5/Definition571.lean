/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Definition571

#doc (Manual) "Virtual representation and its character" =>

# Virtual representation and its character
%%%
tag := "Chapter5/Definition5.7.1"
number := false
%%%

**Definition 5.7.1.** A **virtual representation** of a finite group $`G` is an integer linear combination of irreducible representations of $`G`, $`V = \sum n_i V_i`, $`n_i \in \mathbb{Z}` (i.e., $`n_i` are not assumed to be nonnegative). The character of $`V` is $`\chi_V := \sum n_i \chi_{V_i}`.

## Formalization
%%%
tag := "Chapter5/Definition5.7.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.VirtualRepresentations.Basic.VirtualRepresentation.character}

{Manual.docstring RepresentationTheory.VirtualRepresentations.Basic.VirtualRepresentation.character_apply}

### Supporting declarations

{Manual.docstring RepresentationTheory.VirtualRepresentations.Basic.VirtualRepresentation}

{Manual.docstring RepresentationTheory.VirtualRepresentations.Basic.VirtualRepresentation.character_single}
