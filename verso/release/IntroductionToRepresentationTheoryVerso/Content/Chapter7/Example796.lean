/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter7.Example796

#doc (Manual) "Exactness properties of Ind, Res, Hom, tensor product" =>

# Exactness properties of Ind, Res, Hom, tensor product
%%%
tag := "Chapter7/Example7.9.6"
number := false
%%%

*Example 7.9.6.* (i) The functors $`\operatorname{Ind}_K^G`, $`\operatorname{Res}_K^G` are exact.

(ii) The functor $`\operatorname{Hom}(X, ?)` is left exact, but not necessarily right exact. To see that it need not be right exact, it suffices to consider the exact sequence

$$`0 \to \mathbb{Z} \to \mathbb{Z} \to \mathbb{Z}/2\mathbb{Z} \to 0`

and to apply the functor $`\operatorname{Hom}(\mathbb{Z}/2\mathbb{Z}, ?)`.

(iii) The functor $`X \otimes_A` for a right $`A`-module $`X` (on the category of left $`A`-modules) is right exact but not necessarily left exact. To see this, it suffices to tensor multiply the above exact sequence by $`\mathbb{Z}/2\mathbb{Z}`.

## Formalization
%%%
tag := "Chapter7/Example7.9.6/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.TensorProduct.BalancedRelations.BalancedTensorQuotient.exact_map}

{Manual.docstring RepresentationTheory.TensorProduct.BalancedRelations.BalancedTensorQuotient.map_mulTwo_not_injective}

{Manual.docstring RepresentationTheory.TensorProduct.BalancedRelations.indFunctor_preservesFiniteLimits_and_colimits_of_finiteIndex}

{Manual.docstring RepresentationTheory.TensorProduct.BalancedRelations.postcomp_intToZModTwo_not_surjective}

{Manual.docstring RepresentationTheory.TensorProduct.BalancedRelations.resFunctor_preservesFiniteLimits_and_colimits}
