/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Problem252

#doc (Manual) "Cyclic representations" =>
# Cyclic representations
%%%
tag := "Chapter2/Problem2.5.2"
number := false
%%%
**Problem 2.5.2.** Let $`V \neq 0` be a representation of $`A`. We say that a vector $`v \in V` is **cyclic** if it generates $`V`, i.e., $`Av = V`. A representation admitting a cyclic vector is said to be **cyclic**. Show the following:

(a) $`V` is irreducible if and only if all nonzero vectors of $`V` are cyclic.

(b) $`V` is cyclic if and only if it is isomorphic to $`A/I`, where $`I` is a left ideal in $`A`.

(c) Give an example of an indecomposable representation which is not cyclic.

Hint: Let $`A = \mathbb{C}[x, y]/I_2`, where $`I_2` is the ideal spanned by homogeneous polynomials of degree $`\geq 2` (so $`A` has a basis $`1, x, y`). Let $`V = A^*` be the space of linear functionals on $`A`, with the action of $`A` given by $`(\rho(a)f)(b) = f(ba)`. Show that $`V` provides such an example.

## Formalization
%%%
tag := "Chapter2/Problem2.5.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.DualModules.RightAlgebraDual.toModuleDual_algebra_smul_apply}

{Manual.docstring RepresentationTheory.Algebra.DualModules.degreeAtLeastTwoIdeal_eq_span_homogeneous}

{Manual.docstring RepresentationTheory.Algebra.DualModules.isSimpleModule_iff_forall_ne_zero_isCyclicVector}

{Manual.docstring RepresentationTheory.Algebra.DualModules.squareZeroPlaneAlgEquivQuotient}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.DualModules.IsCyclicModule}

{Manual.docstring RepresentationTheory.Algebra.DualModules.IsCyclicVector}

{Manual.docstring RepresentationTheory.Algebra.DualModules.RightAlgebraDual}

{Manual.docstring RepresentationTheory.Algebra.DualModules.auxiliaryModuleProperty_and_not_isCyclicModule}

{Manual.docstring RepresentationTheory.Algebra.DualModules.isCyclicModule_iff_nonempty_linearEquiv_quotient}

{Manual.docstring RepresentationTheory.Algebra.DualModules.squareZeroPlaneBasis}
