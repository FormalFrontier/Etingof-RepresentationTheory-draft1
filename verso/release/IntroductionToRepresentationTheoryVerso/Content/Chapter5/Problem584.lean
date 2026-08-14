/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Problem584

#doc (Manual) "Transitivity of induction: Ind\\_H^G Ind\\_K^H V \u2245 Ind\\_K^G V" =>

# Transitivity of induction: Ind\_H^G Ind\_K^H V ≅ Ind\_K^G V
%%%
tag := "Chapter5/Problem5.8.4"
number := false
%%%

**Problem 5.8.4.** Check that if $`K \subset H \subset G` are groups and if $`V` is a representation of $`K`, then $`\operatorname{Ind}_H^G \operatorname{Ind}_K^H V` is isomorphic to $`\operatorname{Ind}_K^G V`.

## Formalization
%%%
tag := "Chapter5/Problem5.8.4/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Induction.Transitivity.Representation.exists_induction_transitivity_intertwiner_of_le}

### Supporting declarations

{Manual.docstring RepresentationTheory.InductionAndCoinduction.finiteIndexInducedIsoCoinduced}
