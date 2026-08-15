/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.DiscussionHookLengthDerivation

#doc (Manual) "Derivation of dimension formula for V\\_lambda and definition of hook" =>

# Derivation of dimension formula for V\_lambda and definition of hook
%%%
tag := "Chapter5/Discussion_hook_length_derivation"
number := false
%%%

Let us use the Frobenius character formula to compute the dimension of $`V_\lambda`. According to the character formula, $`\dim V_\lambda` is the coefficient of $`x^{\lambda + \rho}` in $`\Delta(x)(x_1 + \cdots + x_N)^n`. Let $`l_j = \lambda_j + N - j`. Then, using the determinant formula for $`\Delta(x)` and expanding the determinant as a sum over permutations, we get

$$`
\dim V_\lambda = \sum_{s \in S_N : l_j \geq N - s(j)} (-1)^s \frac{n!}{\prod_j (l_j - N + s(j))!}
`

$$`
= \frac{n!}{l_1! \ldots l_N!} \sum_{s \in S_N} (-1)^s \prod_j l_j(l_j - 1) \ldots (l_j - N + s(j) + 1)
`

$$`
= \frac{n!}{\prod_j l_j!} \det(l_j(l_j - 1) \ldots (l_j - N + i + 1)).
`

Using column reduction and the Vandermonde determinant formula, we see from this expression that

$$`
(5.17.1) \qquad \dim V_\lambda = \frac{n!}{\prod_j l_j!} \det(l_j^{N-i}) = \frac{n!}{\prod_j l_j!} \prod_{1 \leq i < j \leq N} (l_i - l_j)
`

(where $`N \geq p`).

In this formula, there are many cancellations. After making some of these cancellations, we obtain the hook length formula. Namely, for a square $`(i, j)` in a Young diagram $`\lambda` ($`i, j \geq 1`, $`i \leq \lambda_j`), define the
**hook** of $`(i, j)` to be the set of all squares $`(i', j')` in $`\lambda` with $`i' \geq i`, $`j' = j` or $`i' = i`, $`j' \geq j`. Let $`h(i, j)` be the length of the hook of $`i, j`, i.e., the number of squares in it.

## Formalization
%%%
tag := "Chapter5/Discussion_hook_length_derivation/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.Combinatorics.PartitionPolynomialAuxiliary.psumPart_partitionChoice_eq_sum_variables_pow}

{Manual.docstring RepresentationTheory.SymmetricPolynomials.Alternant.partitionExpansionCoeff}
