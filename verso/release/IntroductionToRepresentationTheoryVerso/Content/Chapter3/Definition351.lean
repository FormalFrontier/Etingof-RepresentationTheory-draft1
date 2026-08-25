/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.Definition351

#doc (Manual) "Radical of a finite dimensional algebra" =>
# Radical of a finite dimensional algebra
%%%
tag := "Chapter3/Definition3.5.1"
number := false
%%%
**Definition 3.5.1.** The **radical** of a finite dimensional algebra $`A` is the set of all elements of $`A` which act by $`0` in all irreducible representations of $`A`. It is denoted $`\operatorname{Rad}(A)`.

## Formalization
%%%
tag := "Chapter3/Definition3.5.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.RingTheory.SimpleModuleAnnihilator.mem_simpleModuleAnnihilator_iff}

### Supporting declarations

{Manual.docstring RepresentationTheory.RingTheory.SimpleModuleAnnihilator.simpleModuleAnnihilator}
