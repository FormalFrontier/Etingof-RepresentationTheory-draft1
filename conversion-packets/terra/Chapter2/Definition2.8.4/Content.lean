import VersoManual

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Definition284

#doc (Manual) "Path algebra of a quiver" =>
# Path algebra of a quiver
%%%
tag := "Chapter2/Definition2.8.4"
number := false
%%%
**Definition 2.8.4.** The **path algebra** $`P_Q` of a quiver $`Q` is the algebra whose basis is formed by oriented paths in $`Q`, including the trivial paths $`p_i`, $`i \in I`, corresponding to the vertices of $`Q`, and multiplication is the concatenation of paths: $`ab` is the path obtained by first tracing $`b` and then $`a`. If two paths cannot be concatenated, the product is defined to be zero.[^Chapter2/Definition2.8.4/footnote-2]

[^Chapter2/Definition2.8.4/footnote-2]: An oriented path is specified by a nonnegative integer $`n`, a sequence of vertices $`i_0, \ldots, i_n`, and a sequence of edges $`e_1, \ldots, e_n` such that each $`e_r` has source $`i_{r-1}` and target $`i_r`. In particular, when $`n = 0`, one still must choose one vertex $`i_0`, which explains why there is one $`p_i` for each $`i \in I`. Two paths $`a, b` can be concatenated to form the path $`ab` if and only if the final target of $`a` equals the first source of $`b`.
