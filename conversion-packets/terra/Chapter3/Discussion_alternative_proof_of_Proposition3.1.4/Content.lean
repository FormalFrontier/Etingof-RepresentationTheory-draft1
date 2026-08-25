import VersoManual

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
