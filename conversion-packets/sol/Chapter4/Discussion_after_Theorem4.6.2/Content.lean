import VersoManual

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter4.DiscussionAfterTheorem462

#doc (Manual) "Complex conjugate representation isomorphic to dual via unitary structure" =>

# Complex conjugate representation isomorphic to dual via unitary structure
%%%
tag := "Chapter4/Discussion_after_Theorem4.6.2"
number := false
%%%

Theorem 4.6.2 implies that if $`V` is a finite dimensional representation of a finite group $`G`, then the **complex conjugate representation** $`\overline{V}` (i.e., the same space $`V` with the same addition and the same action of $`G`, but complex conjugate action of scalars) is isomorphic to the dual representation $`V^*`. Indeed, a homomorphism of representations $`\overline{V} \to V^*` is obviously the same thing as an invariant sesquilinear form on $`V` (i.e., a form additive on both arguments which is linear on the first one and antilinear on the second one), and an isomorphism is the same thing as a nondegenerate invariant sesquilinear form. So one can use a unitary structure on $`V` to define an isomorphism $`\overline{V} \to V^*`.
