/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Problem5241

#doc (Manual) "V'\\_lambda \u2245 V\\_lambda and V\\_lambda \u2297 C\\_- = V\\_\\{lambda\\*\\}" =>

# V'\_lambda ≅ V\_lambda and V\_lambda ⊗ C\_- = V\_\{lambda\*\}
%%%
tag := "Chapter5/Problem5.24.1"
number := false
%%%

*Problem 5.24.1.* (a) Show that the $`S_n`-representation

$$`V'_\lambda := \mathbb{C}[S_n] b_\lambda a_\lambda`

is isomorphic to $`V_\lambda`.

Hint: Define $`S_n`-homomorphisms $`f : V_\lambda \to V'_\lambda` and $`g : V'_\lambda \to V_\lambda` by the formulas $`f(x) = x a_\lambda` and $`g(y) = y b_\lambda`, and show that they are inverse to each other up to a nonzero scalar.

(b) Let $`\phi : \mathbb{C}[S_n] \to \mathbb{C}[S_n]` be the automorphism sending $`s` to $`(-1)^s s` for any permutation $`s`. Show that $`\phi` maps any representation $`V` of $`S_n` to $`V \otimes \mathbb{C}_-`. Show also that $`\phi(\mathbb{C}[S_n] a) = \mathbb{C}[S_n] \phi(a)`, for $`a \in \mathbb{C}[S_n]`. Use (a) to deduce that $`V_\lambda \otimes \mathbb{C}_- = V_{\lambda^*}`, where $`\lambda^*` is the conjugate partition to $`\lambda`, obtained by reflecting the Young diagram of $`\lambda`.

## Formalization
%%%
tag := "Chapter5/Problem5.24.1/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.SymmetricGroup.PartitionSubmodules.exists_equivariantMap}

{Manual.docstring RepresentationTheory.SymmetricGroup.PartitionSubmodules.partitionSubmodule}

{Manual.docstring RepresentationTheory.SymmetricGroupAlgebra.SignTwist.Partition.selfMap}

{Manual.docstring RepresentationTheory.SymmetricGroupAlgebra.SignTwist.exists_signTwistedEquivariantMap}

{Manual.docstring RepresentationTheory.SymmetricGroupAlgebra.SignTwist.signTwistAlgHom}

{Manual.docstring RepresentationTheory.SymmetricGroupAlgebra.SignTwist.signTwistAlgHom_apply_of}

{Manual.docstring RepresentationTheory.SymmetricGroupAlgebra.SignTwist.signTwistAlgHom_apply_of_smul}

{Manual.docstring RepresentationTheory.SymmetricGroupAlgebra.SignTwist.signTwistAlgHom_bijective}

{Manual.docstring RepresentationTheory.SymmetricGroupAlgebra.SignTwist.signTwistAlgHom_map_span_singleton}
