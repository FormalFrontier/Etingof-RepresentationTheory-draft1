/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.DiscussionProofOfTheorem5122

#doc (Manual) "Proof of Theorem 5.12.2 using Lemmas 5.13.1-5.13.4" =>

# Proof of Theorem 5.12.2 using Lemmas 5.13.1-5.13.4
%%%
tag := "Chapter5/Discussion_proof_of_Theorem5.12.2"
number := false
%%%

Now we are ready to prove Theorem 5.12.2. Let $`\lambda \geq \mu`. Then by Lemmas 5.13.3 and 5.13.4

$$`\operatorname{Hom}_{S_n}(V_\lambda, V_\mu) = \operatorname{Hom}_{S_n}(\mathbb{C}[S_n]c_\lambda, \mathbb{C}[S_n]c_\mu) = c_\lambda \mathbb{C}[S_n] c_\mu.`

The latter space is zero for $`\lambda > \mu` by Lemma 5.13.2 and 1-dimensional if $`\lambda = \mu` by Lemmas 5.13.1 and 5.13.3. Therefore, $`V_\lambda` are irreducible, and $`V_\lambda` is not isomorphic to $`V_\mu` if $`\lambda \neq \mu`. Since the number of partitions equals the number of conjugacy classes in $`S_n`, the representations $`V_\lambda` exhaust all the irreducible representations of $`S_n`. The theorem is proved.

## Formalization
%%%
tag := "Chapter5/Discussion_proof_of_Theorem5.12.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.PartitionAuxiliary.partitionSubmodule_isSimpleModule}

{Manual.docstring RepresentationTheory.PartitionLinearEquivBoundsAndMonoidAlgebra.isEmpty_linearEquiv_of_ne_partition}

{Manual.docstring RepresentationTheory.SimpleModule.SubtypeRepresentation.exists_linearEquiv_to_subtype}

### Supporting declarations

{Manual.docstring RepresentationTheory.AuxiliarySubmodules.indexedSubmodule_isSimple}

{Manual.docstring RepresentationTheory.AuxiliarySubmodules.product_sq_eq_smul}
