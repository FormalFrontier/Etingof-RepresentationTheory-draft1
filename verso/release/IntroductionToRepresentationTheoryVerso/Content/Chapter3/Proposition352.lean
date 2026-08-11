/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.Proposition352

#doc (Manual) "Rad(A) is a two-sided ideal" =>
# Rad(A) is a two-sided ideal
%%%
tag := "Chapter3/Proposition3.5.2"
number := false
%%%
**Proposition 3.5.2.** _$`\operatorname{Rad}(A)` is a two-sided ideal._

**Proof.** Easy. $`\square`

## Formalization
%%%
tag := "Chapter3/Proposition3.5.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.RingTheory.JacobsonRadical.TwoSided.jacobson_isTwoSided}

{Manual.docstring RepresentationTheory.RingTheory.JacobsonRadical.TwoSided.mul_mem_jacobson}
