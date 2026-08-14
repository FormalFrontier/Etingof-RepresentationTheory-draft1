/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter9.Problem953

#doc (Manual) "Blocks and indecomposable central idempotents" =>

# Blocks and indecomposable central idempotents
%%%
tag := "Chapter9/Problem9.5.3"
number := false
%%%

*Problem 9.5.3.* (i) Show that there is a natural bijection between blocks of $`\mathcal{C}` and indecomposable central idempotents $`e_k` of $`A` (i.e., ones that cannot be nontrivially split in a sum of two central idempotents), such that $`\mathcal{C}_k` is the category of finite dimensional $`e_k A`-modules.

(ii) Show that any indecomposable object of $`\mathcal{C}` lies in some $`\mathcal{C}_k` and that $`\operatorname{Hom}(M, N) = 0` if $`M \in \mathcal{C}_k`, $`N \in \mathcal{C}_l`, $`k \neq l`. Thus, $`\mathcal{C} = \bigoplus_{k \in B} \mathcal{C}_k`.

(iii) Determine the blocks in the category of left $`A`-modules for $`A = k[S_3]`, where $`k` is of characteristic 2.

## Formalization
%%%
tag := "Chapter9/Problem9.5.3/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Category.ModuleCat.RingElementActions.hom_subsingleton_of_simpleModule_conditions}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.Category.ModuleCat.RingElementActions.exists_simpleModule_with_condition_of_indecomposable}

{Manual.docstring RepresentationTheory.PermutationRepresentation.CharTwo.associatedType_card_eq_two}

{Manual.docstring RepresentationTheory.PermutationRepresentation.CharTwo.nonempty_algEquiv_matrix_prod_auxiliaryAlgebra}

{Manual.docstring RepresentationTheory.PermutationRepresentation.CharTwo.simpleModule_iso_distinguished_or_oneDimensional}
