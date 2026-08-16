/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.Problem394

#doc (Manual) "Formal deformations of representations" =>

# Formal deformations of representations
%%%
tag := "Chapter3/Problem3.9.4"
number := false
%%%
**Problem 3.9.4.** Let $`A` be an algebra, and let $`V` be a representation of $`A`. Let $`\rho : A \to \operatorname{End} V`. A formal deformation of $`V` is a formal series

$$`\tilde{\rho} = \rho_0 + t\rho_1 + \cdots + t^n \rho_n + \ldots,`

where $`\rho_i : A \to \operatorname{End}(V)` are linear maps, $`\rho_0 = \rho`, and $`\tilde{\rho}(ab) = \tilde{\rho}(a)\tilde{\rho}(b)`.

If $`b(t) = 1 + b_1 t + b_2 t^2 + \ldots`, where $`b_i \in \operatorname{End}(V)`, and $`\tilde{\rho}` is a formal deformation of $`\rho`, then $`b\tilde{\rho}b^{-1}` is also a deformation of $`\rho`, which is said to be isomorphic to $`\tilde{\rho}`.

(a) Show that if $`\operatorname{Ext}^1(V, V) = 0`, then any deformation of $`\rho` is trivial, i.e., isomorphic to $`\rho`.

(b) Is the converse to (a) true? (Consider the algebra of dual numbers $`A = k[x]/x^2`.)

## Formalization
%%%
tag := "Chapter3/Problem3.9.4/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Module.FormalDeformations.auxiliaryDeformationProperty_of_auxiliaryType_subsingleton}

{Manual.docstring RepresentationTheory.Algebra.Module.FormalDeformations.canonicalDeformation}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.Module.FormalDeformations.AuxiliaryDeformationProperty}

{Manual.docstring RepresentationTheory.Algebra.Module.FormalDeformations.AuxiliaryDeformationRel}

{Manual.docstring RepresentationTheory.Algebra.Module.FormalDeformations.FormalRepresentationDeformation}
