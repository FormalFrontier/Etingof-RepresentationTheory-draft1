/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso Genre

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Example233

#doc (Manual) "Examples of representations: zero, regular, k, free algebra" =>
# Examples of representations: zero, regular, k, free algebra
%%%
tag := "Chapter2/Example2.3.3"
number := false
%%%
*Example 2.3.3.*

1. $`V = 0`.

2. $`V = A`, and $`\rho : A \to \operatorname{End} A` is defined as follows: $`\rho(a)` is the operator of left multiplication by $`a`, so that $`\rho(a)b = ab` (the usual product). This representation is called the *regular representation* of $`A`. Similarly, one can equip $`A` with a structure of a right $`A`-module by setting $`\rho(a)b := ba`.

3. $`A = k`. Then a representation of $`A` is simply a vector space over $`k`.

4. $`A = k\langle x_1, \ldots, x_n \rangle`. Then a representation of $`A` is just a vector space $`V` over $`k` with a collection of arbitrary linear operators $`\rho(x_1), \ldots, \rho(x_n) : V \to V` (explain why!).

## Formalization
%%%
tag := "Chapter2/Example2.3.3/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Ring.ModuleStructures.punitModule}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.ModuleActions.RingAddCommGroupAuxiliary}

{Manual.docstring RepresentationTheory.Algebra.Ring.ModuleStructures.op_smul_eq_mul}

{Manual.docstring RepresentationTheory.Algebra.Ring.ModuleStructures.oppositeSelfModule}

{Manual.docstring RepresentationTheory.Algebra.Ring.ModuleStructures.selfModule}
