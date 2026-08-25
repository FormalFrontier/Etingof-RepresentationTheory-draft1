/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter8.Problem827

#doc (Manual) "Computing Tor and Ext for abelian groups and polynomial modules" =>

# Computing Tor and Ext for abelian groups and polynomial modules
%%%
tag := "Chapter8/Problem8.2.7"
number := false
%%%

*Problem 8.2.7.* (i) Let $`A = \mathbb{Z}` and let $`M, N` be finitely generated abelian groups. Compute $`\operatorname{Tor}_i(M, N)`, $`\operatorname{Ext}^i(M, N)` (Hint: Reduce to the case of cyclic groups using the classification theorem for finite abelian groups.)

(ii) Do the same for $`A = k[x]` and $`M, N` being any finitely generated $`A`-modules.

## Formalization
%%%
tag := "Chapter8/Problem8.2.7/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Auxiliary.IntegerModuleStructure.auxiliaryFiniteIntModuleIndexZeroOneEquivsAndAddTwoSubsingleton}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.Auxiliary.GcdZModEquivalences.Algebra.Auxiliary.exists_gcdZModComponentEquivalences_and_higher_subsingleton}

{Manual.docstring RepresentationTheory.Auxiliary.PolynomialModuleIndexedTypes.Auxiliary.finitePolynomialModules_indexZeroOne_addEquiv_and_indexAddTwo_subsingleton}

{Manual.docstring RepresentationTheory.Auxiliary.PolynomialModuleQuotientEquivalences.auxiliaryDegreeZeroDegreeOneAndHigherSubsingleton}
