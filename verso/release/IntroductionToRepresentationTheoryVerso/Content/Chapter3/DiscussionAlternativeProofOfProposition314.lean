/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.DiscussionAlternativeProofOfProposition314

#doc (Manual) "Alternative proof of Proposition 3.1.4 using Hom decomposition" =>
# Alternative proof of Proposition 3.1.4 using Hom decomposition
%%%
tag := "Chapter3/Discussion_alternative_proof_of_Proposition3.1.4"
number := false
%%%
Here is an alternative proof of Proposition 3.1.4.[^Chapter3/Discussion_alternative_proof_of_Proposition3.1.4/footnote-2]

By Remark 3.1.3, if $`V = \bigoplus_X V_X \otimes X` and $`U = \bigoplus_X U_X \otimes X` for some vector spaces $`V_X` and $`U_X`, then we have a natural isomorphism

$$`\operatorname{Hom}_A(V, U) \cong \prod_X \operatorname{Hom}(V_X, U_X).`

Now let $`f : V \to U` correspond to the tuple $`(f_X : V_X \to U_X)`. Then $`f` is injective (respectively surjective, an isomorphism) if and only if all the $`f_X` are.

Now, suppose $`V = \bigoplus_{i \in I} V_i` with $`V_i` irreducible, and $`f : V \to U` is a surjective homomorphism.

[^Chapter3/Discussion_alternative_proof_of_Proposition3.1.4/footnote-2]: We thank B. Poonen for this argument

## Formalization
%%%
tag := "Chapter3/Discussion_alternative_proof_of_Proposition3.1.4/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Module.SemisimpleHomDecomposition.bijective_iff_forall_bijective_homMultiplicityMap}

{Manual.docstring RepresentationTheory.Module.SemisimpleHomDecomposition.homEquivMultiplicityMaps}

{Manual.docstring RepresentationTheory.Module.SemisimpleHomDecomposition.homEquivMultiplicityMaps_apply_apply}

{Manual.docstring RepresentationTheory.Module.SemisimpleHomDecomposition.homMultiplicityMap_comp}

{Manual.docstring RepresentationTheory.Module.SemisimpleHomDecomposition.homMultiplicityMap_id}

{Manual.docstring RepresentationTheory.Module.SemisimpleHomDecomposition.injective_iff_forall_injective_homMultiplicityMap}

{Manual.docstring RepresentationTheory.Module.SemisimpleHomDecomposition.surjective_iff_forall_surjective_homMultiplicityMap}

### Supporting declarations

{Manual.docstring RepresentationTheory.Module.SemisimpleHomDecomposition.homMultiplicityMap}

{Manual.docstring RepresentationTheory.Module.SemisimpleHomDecomposition.homMultiplicityMap_apply_apply}
