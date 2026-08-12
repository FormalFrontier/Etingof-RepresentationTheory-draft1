/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso Genre

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Definition231

#doc (Manual) "Representation of an algebra (left A-module)" =>
# Representation of an algebra (left A-module)
%%%
tag := "Chapter2/Definition2.3.1"
number := false
%%%

## 2.3. Representations
%%%
tag := "Chapter2/Definition2.3.1/heading-1"
%%%

*Definition 2.3.1.* A *representation* of an algebra $`A` (also called a *left $`A`-module*) is a vector space $`V` together with a homomorphism of algebras $`\rho : A \to \operatorname{End} V`.

Similarly, a *right $`A`-module* is a space $`V` equipped with an antihomomorphism $`\rho : A \to \operatorname{End} V`; i.e., $`\rho` satisfies $`\rho(ab) = \rho(b)\rho(a)` and $`\rho(1) = 1`.

The usual abbreviated notation for $`\rho(a)v` is $`av` for a left module and $`va` for a right module. Then the property that $`\rho` is an (anti)homomorphism can be written as a kind of associativity law: $`(ab)v = a(bv)` for left modules, and $`(va)b = v(ab)` for right modules.

## Formalization
%%%
tag := "Chapter2/Definition2.3.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.ModuleActions.RingActionStructure.actionAlgHom}

{Manual.docstring RepresentationTheory.Algebra.ModuleActions.RingActionStructure.actionAlgHom_eq}

{Manual.docstring RepresentationTheory.Algebra.ModuleActions.RingActionStructure.moduleOfAlgHom}

{Manual.docstring RepresentationTheory.Algebra.ModuleActions.RingActionStructure.moduleOfAlgHom_actionAlgHom}

{Manual.docstring RepresentationTheory.Algebra.ModuleActions.RingActionStructure.mul_smul}

{Manual.docstring RepresentationTheory.Algebra.ModuleActions.RingActionStructure.op_mul_smul}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.ModuleActions.RingActionStructure.oppositeActionAlgHom}

{Manual.docstring RepresentationTheory.Algebra.ModuleActions.RingActionStructureAux}
