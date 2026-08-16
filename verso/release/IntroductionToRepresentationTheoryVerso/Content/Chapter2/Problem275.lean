/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Problem275

#doc (Manual) "Center, ideals, and representations of the q-Weyl algebra" =>
# Center, ideals, and representations of the q-Weyl algebra
%%%
tag := "Chapter2/Problem2.7.5"
number := false
%%%
**Problem 2.7.5.** Let $`q` be a nonzero complex number, and let $`A` be the $`q`-Weyl algebra over $`\mathbb{C}`.

(a) What is the center of $`A` for different $`q`? If $`q` is not a root of unity, what are the two-sided ideals in $`A`?

(b) For which $`q` does this algebra have finite dimensional representations?

Hint: Use determinants.

(c) Find all finite dimensional irreducible representations of $`A` for such $`q`.

Hint: This is similar to part (c) of the previous problem.

## Formalization
%%%
tag := "Chapter2/Problem2.7.5/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.ParameterizedAlgebra.FiniteSimpleModules.center_eq_adjoin_generators_of_isOfFinOrder}

{Manual.docstring RepresentationTheory.ParameterizedAlgebra.FiniteSimpleModules.center_eq_bot_of_not_isOfFinOrder}

{Manual.docstring RepresentationTheory.ParameterizedAlgebra.FiniteSimpleModules.finrank_eq_orderOf}

{Manual.docstring RepresentationTheory.ParameterizedAlgebra.FiniteSimpleModules.isSimpleRing_of_not_isOfFinOrder}

{Manual.docstring RepresentationTheory.ParameterizedAlgebra.FiniteSimpleModules.pow_finrank_eq_one}

{Manual.docstring RepresentationTheory.ParameterizedAlgebra.ModelModules.finFunctionModule_isSimple}

{Manual.docstring RepresentationTheory.ParameterizedAlgebra.SimpleModuleClassification.exists_model_equiv}

{Manual.docstring RepresentationTheory.ParameterizedAlgebra.SimpleModuleClassification.finiteSimpleModule_finrank_eq_orderOf}

{Manual.docstring RepresentationTheory.QuantumTorus.FiniteOrderModuleEquivalences.nonempty_moduleLinearEquiv_iff}

### Supporting declarations

{Manual.docstring RepresentationTheory.ParameterizedAlgebra.SimpleModuleClassification.exists_model_parameters_unique}

{Manual.docstring RepresentationTheory.ParameterizedAlgebra.SimpleModuleExistence.isOfFinOrder_iff_exists_nontrivial_finiteModule}

{Manual.docstring RepresentationTheory.QuantumTorus.FiniteOrderModules.finrank_finFunction}
