/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.DiscussionFaithfulExample

#doc (Manual) "Faithful representations of the Weyl algebra in different characteristics" =>
# Faithful representations of the Weyl algebra in different characteristics
%%%
tag := "Chapter2/Discussion_faithful_example"
number := false
%%%
For example, $`k[t]` is a faithful representation of the Weyl algebra if $`k` has characteristic zero (check it!), but not in characteristic $`p`, where $`(d/dt)^p Q = 0` for any polynomial $`Q`. However, the representation $`E = t^a k[a][t, t^{-1}]`, as we've seen, is faithful in any characteristic.

## Formalization
%%%
tag := "Chapter2/Discussion_faithful_example/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.IntegerIndexedPolynomialOperators.operatorRepresentation_injective}

{Manual.docstring RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.comparisonMap_not_injective_of_charP}

{Manual.docstring RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.toPolynomialEnd_injective}

{Manual.docstring RepresentationTheory.FreeAlgebra.PolynomialOperators.derivative_iterate_prime_eq_zero}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.IntegerIndexedPolynomialOperators.operatorRepresentation_injective_and_comparisonMap_not_injective}

{Manual.docstring RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.toPolynomialEnd_power_second_eq_zero}
