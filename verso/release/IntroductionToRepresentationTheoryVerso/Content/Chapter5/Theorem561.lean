/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Theorem561

#doc (Manual) "Irreducible representations of G x H are tensor products V\\_i \u2297 W\\_j" =>

# Irreducible representations of G x H are tensor products V\_i ⊗ W\_j
%%%
tag := "Chapter5/Theorem5.6.1"
number := false
%%%

**Theorem 5.6.1.** _Let $`G, H` be finite groups, let $`\{V_i\}` be the irreducible representations of $`G` over a field $`k` (of any characteristic), and let $`\{W_j\}` be the irreducible representations of $`H` over $`k`. Then the irreducible representations of $`G \times H` over $`k` are $`\{V_i \otimes W_j\}`._

**Proof.** This follows from Theorem 3.10.2. $`\square`

## Formalization
%%%
tag := "Chapter5/Theorem5.6.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.AuxiliaryTensorProductRepresentations.auxiliary_exists_tensorProduct}

{Manual.docstring RepresentationTheory.AuxiliaryTensorProductRepresentations.auxiliary_tensorProduct_characterization}

{Manual.docstring RepresentationTheory.AuxiliaryTensorProductRepresentations.isAuxiliary_tensorProductRepresentation}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.Module.TensorProductSimplicity.exists_tensorFactorization_of_simpleBimodule}

{Manual.docstring RepresentationTheory.Algebra.Module.TensorProductSimplicity.submodule_eq_bot_or_top_of_tensorActions}
