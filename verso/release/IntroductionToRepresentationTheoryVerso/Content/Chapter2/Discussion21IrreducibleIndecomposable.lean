/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Discussion21IrreducibleIndecomposable

#doc (Manual) "Irreducible and indecomposable representations; typical problems of representation theory" =>
# Irreducible and indecomposable representations; typical problems of representation theory
%%%
tag := "Chapter2/Discussion_2.1_irreducible_indecomposable"
number := false
%%%
A nonzero representation $`V` of $`A` is said to be *irreducible* if its only subrepresentations
are $`0` and $`V` itself, and it is said to be *indecomposable* if it cannot be written as a
direct sum of two nonzero subrepresentations. Obviously, irreducible implies indecomposable, but
not vice versa.

Typical problems of representation theory are as follows:

(1) Classify irreducible representations of a given algebra $`A`.

(2) Classify indecomposable representations of $`A`.

(3) Do (1) and (2) restricting to finite dimensional representations.

As mentioned above, the algebra $`A` is often given to us by generators and relations. For
example, the universal enveloping algebra $`U` of the Lie algebra $`\mathfrak{sl}(2)` is generated
by $`h, e, f` with defining relations

$$`(2.1.1) \qquad he - eh = 2e, \quad hf - fh = -2f, \quad ef - fe = h.`

This means that the problem of finding, say, $`N`-dimensional representations of $`A` reduces to
solving a bunch of nonlinear algebraic equations with respect to a bunch of unknown $`N \times N`
matrices, for example system (2.1.1) with respect to unknown matrices $`h, e, f`.

It is really striking that such, at first glance hopelessly complicated, systems of equations can
in fact be solved completely by methods of representation theory! For example, we will prove the
following theorem.

## Formalization
%%%
tag := "Chapter2/Discussion_2.1_irreducible_indecomposable/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.LinearAlgebra.ModuleConditions.ModuleCondition}

{Manual.docstring RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate}

{Manual.docstring RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate.not_exists_complementarySubmodules}

{Manual.docstring RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate.of_isSimpleModule}

{Manual.docstring RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.isIndecomposableModule_and_not_isSimpleModule_jordanBlock_two}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.ModuleActions.RingActionStructure.actionAlgHom}

{Manual.docstring RepresentationTheory.FreeAlgebra.RelationQuotient.FreeAlgebra.AuxiliaryType.algHom_ext}

{Manual.docstring RepresentationTheory.FreeAlgebra.RelationQuotient.FreeAlgebra.AuxiliaryType.lift}

{Manual.docstring RepresentationTheory.LieAlgebra.SpecialLinearPresentation.algEquiv}

{Manual.docstring RepresentationTheory.LieAlgebra.SpecialLinearPresentation.map_apply_aux1}

{Manual.docstring RepresentationTheory.LieAlgebra.SpecialLinearPresentation.map_apply_aux2}

{Manual.docstring RepresentationTheory.LieAlgebra.SpecialLinearPresentation.map_apply_aux3}
