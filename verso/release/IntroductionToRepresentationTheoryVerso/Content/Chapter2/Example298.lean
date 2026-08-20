/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Example298

#doc (Manual) "Examples of representations of Lie algebras" =>
# Examples of representations of Lie algebras
%%%
tag := "Chapter2/Example2.9.8"
number := false
%%%
**Example 2.9.8.** Some examples of representations of Lie algebras are:

(1) $`V = 0`.

(2) Any vector space $`V` with $`\rho = 0` (the trivial representation).

(3) The adjoint representation $`V = \mathfrak{g}` with $`\rho(a)(b) := [a, b]`. That this is a representation follows from equation (2.9.1). Thus, the meaning of the Jacobi identity is that it is equivalent to the existence of the adjoint representation.

It turns out that a representation of a Lie algebra $`\mathfrak{g}` is the same thing as a representation of a certain associative algebra $`U(\mathfrak{g})`. Thus, as with quivers, we can view the theory of representations of Lie algebras as a part of the theory of representations of associative algebras.

## Formalization
%%%
tag := "Chapter2/Example2.9.8/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Lie.Module.Examples.adjointRepresentation_apply}

{Manual.docstring RepresentationTheory.Algebra.Lie.Module.Examples.adjointRepresentation_bracket}

{Manual.docstring RepresentationTheory.Algebra.Lie.Module.Examples.punitTrivialModuleProperty}

{Manual.docstring RepresentationTheory.Algebra.Lie.UniversalEnveloping.representationAlgHomEquiv}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.Lie.Module.Examples.adjointRepresentation}

{Manual.docstring RepresentationTheory.Algebra.Lie.Module.Examples.punitTrivialModule_subsingleton}

{Manual.docstring RepresentationTheory.Algebra.Lie.Module.Examples.selfProperty}

{Manual.docstring RepresentationTheory.Algebra.Lie.Module.Examples.trivialModuleProperty}

{Manual.docstring RepresentationTheory.Algebra.Lie.Module.Examples.trivialModule_bracket_eq_zero}
