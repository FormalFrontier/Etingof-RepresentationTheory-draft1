import VersoManual

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Definition2111

#doc (Manual) "Tensor product of vector spaces" =>
# Tensor product of vector spaces
%%%
tag := "Chapter2/Definition2.11.1"
number := false
%%%
**Definition 2.11.1.** The **tensor product** $`V \otimes W` of vector spaces $`V` and $`W` over a field $`k` is the quotient of the space $`V * W` whose basis is given by formal symbols $`v \otimes w`, $`v \in V`, $`w \in W`, by the subspace spanned by the elements

$$`(v_1 + v_2) \otimes w - v_1 \otimes w - v_2 \otimes w,`
$$`v \otimes (w_1 + w_2) - v \otimes w_1 - v \otimes w_2,`
$$`av \otimes w - a(v \otimes w),`
$$`v \otimes aw - a(v \otimes w),`

where $`v \in V, w \in W, a \in k`.
