/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Definition541

#doc (Manual) "Solvable group" =>

# Solvable group
%%%
tag := "Chapter5/Definition5.4.1"
number := false
%%%

**Definition 5.4.1.** A group $`G` is called **solvable** if there exists a series of nested normal subgroups

$$`\{e\} = G_1 \lhd G_2 \lhd \ldots \lhd G_n = G`

where $`G_{i+1}/G_i` is abelian for all $`1 \leq i \leq n - 1`.

## Formalization
%%%
tag := "Chapter5/Definition5.4.1/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.SolvableGroups.Series.Auxiliary}

{Manual.docstring RepresentationTheory.SolvableGroups.Series.auxiliary_iff_isSolvable}

{Manual.docstring RepresentationTheory.SolvableGroups.Series.normal_comap_of_bracket_le}

{Manual.docstring RepresentationTheory.SolvableGroups.Series.quotient_isMulCommutative_iff_bracket_le}
