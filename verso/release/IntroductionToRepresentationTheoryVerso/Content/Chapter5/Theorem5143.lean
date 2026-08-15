/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Theorem5143

#doc (Manual) "Character of U\\_lambda as coefficient of x^lambda in product of power sums" =>

# Character of U\_lambda as coefficient of x^lambda in product of power sums
%%%
tag := "Chapter5/Theorem5.14.3"
number := false
%%%

**Theorem 5.14.3.** _Let $`N \geq p` (where $`p` is the number of parts of $`\lambda`). Then $`\chi_{U_\lambda}(C_\mathbf{i})` is the coefficient$`{}^1` of $`x^\lambda := \prod_j x_j^{\lambda_j}` in the polynomial_

$$`\prod_{m \geq 1} H_m(x)^{i_m}.`

**Proof.** The proof is obtained easily from the Frobenius formula. Namely, $`\chi_{U_\lambda}(C_\mathbf{i})` is the number of elements $`x \in S_n` such that $`xgx^{-1} \in P_\lambda` (for a representative $`g \in C_\mathbf{i}`), divided by $`|P_\lambda|`. The order of $`P_\lambda` is $`\prod_i \lambda_i!`, and the number of elements $`x` such that $`xgx^{-1} \in P_\lambda` is the number of elements in $`P_\lambda` conjugate to $`g` (i.e., $`|C_\mathbf{i} \cap P_\lambda|`) times the order of the centralizer $`Z_g` of $`g` (which is $`n!/|C_\mathbf{i}|`). Thus,

$$`\chi_{U_\lambda}(C_\mathbf{i}) = \frac{|Z_g|}{\prod_j \lambda_j!} |C_\mathbf{i} \cap P_\lambda|.`

Now, it is easy to see that the centralizer $`Z_g` of $`g` is isomorphic to

$$`\prod_m S_{i_m} \ltimes (\mathbb{Z}/m\mathbb{Z})^{i_m},`

so

$$`|Z_g| = \prod_m m^{i_m} i_m!,`

and we get

$$`\chi_{U_\lambda}(C_\mathbf{i}) = \frac{\prod_m m^{i_m} i_m!}{\prod_j \lambda_j!} |C_\mathbf{i} \cap P_\lambda|.`

Now, since $`P_\lambda = \prod_j S_{\lambda_j}`, we have

$$`|C_\mathbf{i} \cap P_\lambda| = \sum_r \prod_{j \geq 1} \frac{\lambda_j!}{\prod_{m \geq 1} m^{r_{jm}} r_{jm}!},`

where $`r = (r_{jm})` runs over all collections of nonnegative integers such that

$$`\sum_m m r_{jm} = \lambda_j, \qquad \sum_j r_{jm} = i_m.`

Indeed, an element of $`C_\mathbf{i}` that is in $`P_\lambda` would define an ordered partition of each $`\lambda_j` into parts (namely, cycle lengths), with $`m` occurring

---

$`{}^1`If $`j > p`, we define $`\lambda_j` to be zero.
$`r_{jm}` times, such that the total (over all $`j`) number of times each part $`m` occurs is $`i_m`. Thus we get

$$`\chi_{U_\lambda}(C_\mathbf{i}) = \sum_r \prod_m \frac{i_m!}{\prod_j r_{jm}!}.`

But this is exactly the coefficient of $`x^\lambda` in

$$`\prod_{m \geq 1} (x_1^m + \cdots + x_N^m)^{i_m}`

($`r_{jm}` is the number of times we take $`x_j^m`). $`\square`

## Formalization
%%%
tag := "Chapter5/Theorem5.14.3/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Permutation.CentralizerCycleFacts.Equiv.Perm.auxiliaryNatValue_eq_cycleType_count_of_two_le}

{Manual.docstring RepresentationTheory.Permutation.CentralizerCycleFacts.Equiv.Perm.auxiliaryNatValue_one_eq_card_fixedPoints}

{Manual.docstring RepresentationTheory.Permutation.CentralizerCycleFacts.Equiv.Perm.card_centralizer_eq_prod_auxiliaryNatValue}

{Manual.docstring RepresentationTheory.Permutation.CentralizerCycleFacts.Equiv.Perm.centralizerMulEquivAuxiliaryProduct}

{Manual.docstring RepresentationTheory.Permutation.CentralizerCycleFacts.Equiv.Perm.centralizerMulEquivFinAuxiliaryProduct}

{Manual.docstring RepresentationTheory.PermutationPolynomialAuxiliary.partitionPermutationValue_eq_coefficient}

### Supporting declarations

{Manual.docstring RepresentationTheory.Permutation.CentralizerCycleFacts.Equiv.Perm.minimalPeriod_eq_card_support_cycleOf}

{Manual.docstring RepresentationTheory.PermutationPolynomialAuxiliary.partitionPermutationValue_eq_card_auxiliary}

{Manual.docstring RepresentationTheory.PermutationPolynomialAuxiliary.partitionPolynomialCoeff_eq_card_auxiliary}
