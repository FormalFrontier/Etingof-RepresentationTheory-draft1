/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Example2314Continued

#doc (Manual) "Representations of group algebras k\\[G\\]" =>
# Representations of group algebras k\[G\]
%%%
tag := "Chapter2/Example2.3.14_continued"
number := false
%%%
3. The group algebra $`A = k[G]`, where $`G` is a group. A representation of $`A` is the same thing as a representation of $`G`, i.e., a vector space $`V` together with a group homomorphism $`\rho : G \to \operatorname{Aut}(V)`, where $`\operatorname{Aut}(V) = GL(V)` denotes the group of invertible linear maps from the space $`V` to itself (the **general linear group** of $`V`).

## Formalization
%%%
tag := "Chapter2/Example2.3.14_continued/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Representation.Equivalences.representationAlgHomEquiv}

{Manual.docstring RepresentationTheory.Algebra.Representation.Equivalences.representationLinearEquivHomEquiv}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.Representation.Equivalences.representationLinearEquivHomEquiv_apply}

{Manual.docstring RepresentationTheory.Algebra.Representation.Equivalences.representationLinearEquivHomEquiv_symm_apply}
