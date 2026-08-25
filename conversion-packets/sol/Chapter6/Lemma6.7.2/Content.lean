import VersoManual

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter6.Lemma672

#doc (Manual) "Lemma 6.7.2: Coxeter element eventually produces a negative coefficient" =>

# Lemma 6.7.2: Coxeter element eventually produces a negative coefficient
%%%
tag := "Chapter6/Lemma6.7.2"
number := false
%%%

*Lemma 6.7.2.* _Let_

$$`
\beta = \sum_i k_i \alpha_i
`

_with $`k_i \geq 0` for all $`i` but not all $`k_i = 0`. Then there is $`n \in \mathbb{N}`, such that_

$$`
c^N \beta
`

_has at least one strictly negative coefficient._

*Proof.* The Coxeter element $`c` belongs to a finite group $`W`. So there is $`M \in \mathbb{N}`, such that

$$`
c^M = 1.
`

We claim that

$$`
1 + c + c^2 + \cdots + c^{M-1} = 0
`

as operators on $`\mathbb{R}^n`. This implies what we need, since $`\beta` has at least one strictly positive coefficient, so one of the elements

$$`
c\beta, c^2 \beta, \ldots, c^{M-1} \beta
`

must have at least one strictly negative coefficient. Furthermore, it is enough to show that $`1` is not an eigenvalue for $`c`, since

$$`
(1 + c + c^2 + \ldots + c^{M-1})v = w \neq 0
`

$$`
\implies cw = c\left(1 + c + c^2 + \cdots + c^{M-1}\right)v
`

$$`
= (c + c^2 + c^3 + \cdots + c^{M-1} + 1)v = w.
`
Assume the contrary, i.e., 1 is an eigenvalue of $`c` and let $`v` be a corresponding eigenvector:

$$`
cv = v \implies s_1 \ldots s_n v = v \iff s_2 \ldots s_n v = s_1 v.
`

But since $`s_i` only changes the $`i`th coordinate of $`v`, we get

$$`
s_1 v = v \quad \text{and} \quad s_2 \ldots s_n v = v.
`

Repeating the same procedure, we get

$$`
s_i v = v
`

for all $`i`. But this means

$$`
B(v, \alpha_i) = 0
`

for all $`i`, and since $`B` is nondegenerate, we get $`v = 0`. But this is a contradiction, since $`v` is an eigenvector. $`\square`
