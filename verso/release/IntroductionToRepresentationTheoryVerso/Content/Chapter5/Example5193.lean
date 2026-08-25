/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Example5193

#doc (Manual) "L\\_lambda for partitions (n) and (1^n): S^nV and \u039b^nV" =>

# L\_lambda for partitions (n) and (1^n): S^nV and Λ^nV
%%%
tag := "Chapter5/Example5.19.3"
number := false
%%%

*Example 5.19.3.* If $`\lambda = (n)`, then $`L_\lambda = S^n V`, and if $`\lambda = (1^n)` ($`n` copies of $`1`), then $`L_\lambda = \wedge^n V`. It was shown in Problem 4.12.3 that these representations are indeed irreducible (except that $`\wedge^n V` is zero if $`n > \dim V`).

## Formalization
%%%
tag := "Chapter5/Example5.19.3/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.exteriorPower_invariantSubmodule_eq_bot_or_top}

{Manual.docstring RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.exteriorPower_subsingleton_of_finrank_lt}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.auxiliarySubmoduleEquivExteriorPower}

{Manual.docstring RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.auxiliarySubmoduleEquivExteriorPower_map}

{Manual.docstring RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.auxiliarySubmoduleEquivSymmetricPower}

{Manual.docstring RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.auxiliarySubmoduleEquivSymmetricPower_map}
