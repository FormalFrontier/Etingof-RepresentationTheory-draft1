/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Remark272

#doc (Manual) "Weyl algebra as algebra of polynomial differential operators" =>
# Weyl algebra as algebra of polynomial differential operators
%%%
tag := "Chapter2/Remark2.7.2"
number := false
%%%
**Remark 2.7.2.** The proof of (i) shows that the Weyl algebra $`A` can be viewed as the algebra of polynomial differential operators in one variable $`t`.

The proof of (i) also brings up the notion of a faithful representation.

## Formalization
%%%
tag := "Chapter2/Remark2.7.2/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.Polynomial.EndomorphismAuxiliary.auxiliaryEndomorphismSubalgebra}

{Manual.docstring RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.auxiliaryAlgEquiv}

{Manual.docstring RepresentationTheory.FreeAlgebra.PolynomialOperators.AuxiliaryAlgebra.auxiliaryMap_range}

{Manual.docstring RepresentationTheory.LinearAlgebra.ModulePredicates.AuxiliaryModulePredicate}
