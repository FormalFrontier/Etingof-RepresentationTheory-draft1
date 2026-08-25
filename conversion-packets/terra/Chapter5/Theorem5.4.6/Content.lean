import VersoManual

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Theorem546

#doc (Manual) "Group with conjugacy class of size p^k is not simple" =>

# Group with conjugacy class of size p^k is not simple
%%%
tag := "Chapter5/Theorem5.4.6"
number := false
%%%

**Theorem 5.4.6.** _Let $`G` be a finite group, and let $`C` be a conjugacy class in $`G` of size $`p^k` where $`p` is a prime and $`k > 0`. Then $`G` has a proper nontrivial normal subgroup (i.e., $`G` is not simple)._

**Proof.** Choose an element $`g \in C`. Since $`g \neq e`, by orthogonality of columns of the character table,

$$`(5.4.1) \qquad \sum_{V \in \operatorname{Irr} G} \dim V \chi_V(g) = 0.`

We can divide $`\operatorname{Irr} G` into three parts:

(1) the trivial representation,

(2) $`D`, the set of irreducible representations whose dimension is divisible by $`p`, and

(3) $`N`, the set of nontrivial irreducible representations whose dimension is not divisible by $`p`.
