import VersoManual

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Discussion5253

#doc (Manual) "Section 5.25.3: Principal series representations \u2014 setup of B, V\\_\\{lambda\\_1,lambda\\_2\\}" =>

# Section 5.25.3: Principal series representations — setup of B, V\_\{lambda\_1,lambda\_2\}
%%%
tag := "Chapter5/Discussion_5.25.3"
number := false
%%%
**5.25.3. Principal series representations.** Let

$$`B \subset G, \quad B = \left\{ \begin{pmatrix} * & * \\ 0 & * \end{pmatrix} \right\}`

(the set of upper triangular matrices); then

$$`|B| = (q - 1)^2 q,`

$$`[B, B] = U = \left\{ \begin{pmatrix} 1 & * \\ 0 & 1 \end{pmatrix} \right\},`

and

$$`B/[B, B] \cong \mathbb{F}_q^\times \times \mathbb{F}_q^\times`

(the isomorphism maps an element of $`B` to its two diagonal entries). Let

$$`\lambda : B \to \mathbb{C}^\times`
be a homomorphism defined by

$$`\lambda\begin{pmatrix} a & b \\ 0 & c \end{pmatrix} = \lambda_1(a)\lambda_2(c)`

for some pair of homomorphisms $`\lambda_1, \lambda_2 : \mathbb{F}_q^\times \to \mathbb{C}^\times`. Define

$$`V_{\lambda_1, \lambda_2} = \operatorname{Ind}_B^G \mathbb{C}_\lambda,`

where $`\mathbb{C}_\lambda` is the 1-dimensional representation of $`B` in which $`B` acts by $`\lambda`. We have

$$`\dim(V_{\lambda_1, \lambda_2}) = \frac{|G|}{|B|} = q + 1.`
