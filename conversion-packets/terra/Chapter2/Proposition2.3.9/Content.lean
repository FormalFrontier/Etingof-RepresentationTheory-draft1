import VersoManual

open Verso Genre

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Proposition239

#doc (Manual) "Schur's lemma" =>
# Schur's lemma
%%%
tag := "Chapter2/Proposition2.3.9"
number := false
%%%
*Proposition 2.3.9* (Schur's lemma). _Let $`V_1, V_2` be representations of an algebra $`A` over any field $`F` (which need not be algebraically closed). Let $`\phi : V_1 \to V_2` be a nonzero homomorphism of representations. Then:_

_(i) If $`V_1` is irreducible, $`\phi` is injective._

_(ii) If $`V_2` is irreducible, $`\phi` is surjective._

_Thus, if both $`V_1` and $`V_2` are irreducible, $`\phi` is an isomorphism._

*Proof.* (i) The kernel $`K` of $`\phi` is a subrepresentation of $`V_1`. Since $`\phi \neq 0`, this subrepresentation cannot be $`V_1`. So by irreducibility of $`V_1` we have $`K = 0`.

(ii) The image $`I` of $`\phi` is a subrepresentation of $`V_2`. Since $`\phi \neq 0`, this subrepresentation cannot be $`0`. So by irreducibility of $`V_2` we have $`I = V_2`. $`\square`
