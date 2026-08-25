/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter7.Example772

#doc (Manual) "Module categories as abelian categories" =>

# Module categories as abelian categories
%%%
tag := "Chapter7/Example7.7.2"
number := false
%%%

*Example 7.7.2.* The category of modules over an algebra $`A` and the category of finite dimensional modules over $`A` are abelian categories.

## Formalization
%%%
tag := "Chapter7/Example7.7.2/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.FiniteDimensional.FGModuleCategory.FGModuleCat.instAbelian_of_finiteDimensional}

{Manual.docstring RepresentationTheory.Algebra.FiniteDimensional.FGModuleCategory.moduleFinite_iff_finiteDimensional}
