/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Theorem5232

#doc (Manual) "Complete reducibility and Peter-Weyl theorem for GL(V) (continues to missing page)" =>

# Complete reducibility and Peter-Weyl theorem for GL(V) (continues to missing page)
%%%
tag := "Chapter5/Theorem5.23.2"
number := false
%%%

*Theorem 5.23.2.* _(i) Every finite dimensional algebraic representation of $`GL(V)` is completely reducible, and decomposes into summands of the form $`L_\lambda` (which are pairwise nonisomorphic)._

_(ii) (The Peter-Weyl theorem for $`GL(V)`) Let $`R` be the algebra of polynomial functions on $`GL(V)`. Then as a representation of $`GL(V) \times GL(V)` (with action $`(\rho(g, h)\phi)(x) = \phi(g^{-1}xh)`, $`g, h, x \in GL(V)`, $`\phi \in R`), $`R` decomposes as_

$$`R = \bigoplus_\lambda L_\lambda^* \otimes L_\lambda,`

_where the summation runs over all $`\lambda`._

## Formalization
%%%
tag := "Chapter5/Theorem5.23.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.AuxiliaryEquivariantDecomposition.auxiliary_nonempty_representationRelation}

### Supporting declarations

{Manual.docstring RepresentationTheory.AuxiliaryRepresentationDecompositions.auxiliary_exists_directSum_representation_decomposition}

{Manual.docstring RepresentationTheory.AuxiliarySemisimpleDecomposition.isSemisimpleModule_of_auxiliary}
