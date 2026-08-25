import VersoManual

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter6.Corollary683

#doc (Manual) "Corollary 6.8.3: Uniqueness of indecomposable with given dimension vector" =>

# Corollary 6.8.3: Uniqueness of indecomposable with given dimension vector
%%%
tag := "Chapter6/Corollary6.8.3"
number := false
%%%

*Corollary 6.8.3.* _Let $`V, V'` be indecomposable representations of $`Q` such that $`d(V) = d(V')`. Then $`V` and $`V'` are isomorphic._
*Proof.* Let $`i` be the smallest integer such that

$$`
d\left(V^{(i)}\right) = \alpha_p.
`

Then we also get $`d\left(V'^{(i)}\right) = \alpha_p`. So

$$`
V'^{(i)} = V^{(i)} =: V^i.
`

Furthermore we have

$$`
V^{(i)} = F_k^+ \ldots F_{n-1}^+ F_n^+ V^{(0)},
`

$$`
V'^{(i)} = F_k^+ \ldots F_{n-1}^+ F_n^+ V'^{(0)}.
`

But both $`V^{(i-1)}, \ldots, V^{(0)}` and $`V'^{(i-1)}, \ldots, V'^{(0)}` have to be surjective at the appropriate vertices. This implies

$$`
F_n^- F_{n-1}^- \ldots F_k^- V^i = \begin{cases} F_n^- F_{n-1}^- \ldots F_k^- F_k^+ \ldots F_{n-1}^+ F_n^+ V^{(0)} = V^{(0)} = V, \\ F_n^- F_{n-1}^- \ldots F_k^- F_k^+ \ldots F_{n-1}^+ F_n^+ V'^{(0)} = V'^{(0)} = V'. \end{cases}
`

$`\square`
