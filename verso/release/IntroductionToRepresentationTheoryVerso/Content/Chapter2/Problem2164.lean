/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Problem2164

#doc (Manual) "Irreducible representations of sl(2) in characteristic p" =>
# Irreducible representations of sl(2) in characteristic p
%%%
tag := "Chapter2/Problem2.16.4"
number := false
%%%
**Problem 2.16.4.** Classify irreducible representations of the Lie algebra $`\mathfrak{sl}(2)` over an algebraically closed field $`k` of characteristic $`p > 2`.

## Formalization
%%%
tag := "Chapter2/Problem2.16.4/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.LieModule.IrreducibleParameterModules.exists_parameterModule_equiv}

{Manual.docstring RepresentationTheory.LieModule.IrreducibleParameterModules.nonempty_parameterEquivWitness_iff}

### Supporting declarations

{Manual.docstring RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.finrank_finFunction}

{Manual.docstring RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.finrank_le_characteristic}

{Manual.docstring RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.isIrreducible_finFunction_of_le_characteristic}

{Manual.docstring RepresentationTheory.LieAlgebra.TwoByTwoMatrixRepresentations.not_forall_finrank_lt_characteristic}

{Manual.docstring RepresentationTheory.LieModule.IrreducibleParameterModules.ModuleParameter}

{Manual.docstring RepresentationTheory.LieModule.IrreducibleParameterModules.isIrreducible_parameterModule}

{Manual.docstring RepresentationTheory.LieModule.IrreducibleParameterModules.parameterModuleLieHom}

{Manual.docstring RepresentationTheory.LieModule.IrreducibleParameterModules.parameterQuotientEquivModuleData}
