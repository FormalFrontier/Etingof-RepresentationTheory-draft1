/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter6.Example649

#doc (Manual) "Example 6.4.9: Roots for A\\_\\{N-1\\} and other Dynkin types" =>

# Example 6.4.9: Roots for A\_\{N-1\} and other Dynkin types
%%%
tag := "Chapter6/Example6.4.9"
number := false
%%%

*Example 6.4.9.* (1) Let $`\Gamma` be of the type $`A_{N-1}`. Then the lattice $`L = \mathbb{Z}^{N-1}` can be realized as a subgroup of the lattice $`\mathbb{Z}^N` by letting $`L \subseteq \mathbb{Z}^N` be the subgroup of all vectors $`(x_1, \ldots, x_N)` such that

$$`
\sum_i x_i = 0.
`

The vectors

$$`
\alpha_1 = (1, -1, 0, \ldots, 0),
`

$$`
\alpha_2 = (0, 1, -1, 0, \ldots, 0),
`

$$`
\vdots
`

$$`
\alpha_{N-1} = (0, \ldots, 0, 1, -1)
`

naturally form a basis of $`L`. Furthermore, the standard inner product

$$`
(x, y) = \sum x_i y_i
`

on $`\mathbb{Z}^N` restricts to the inner product $`B` given by $`\Gamma` on $`L`, since it takes the same values on the basis vectors:

$$`
(\alpha_i, \alpha_i) = 2,
`

$$`
(\alpha_i, \alpha_j) = \begin{cases} -1, & i, j \text{ are adjacent}, \\ 0, & \text{otherwise}. \end{cases}
`

This means that vectors of the form

$$`
(0, \ldots, 0, 1, 0, \ldots, 0, -1, 0, \ldots, 0) = \alpha_i + \alpha_{i+1} + \cdots + \alpha_{j-1}
`
and

$$`
(0, \ldots, 0, -1, 0, \ldots, 0, 1, 0, \ldots, 0) = -(\alpha_i + \alpha_{i+1} + \cdots + \alpha_{j-1})
`

are the roots of $`L`. Therefore the number of positive roots in $`L` equals

$$`
\frac{N(N-1)}{2}.
`

Thus, $`A_n` has $`n(n+1)/2` positive roots.

(2) As a fact, we also state the number of positive roots in the other Dynkin diagrams:

* $`D_n`: $`n(n-1)` roots,
* $`E_6`: 36 roots,
* $`E_7`: 63 roots,
* $`E_8`: 120 roots.

## Formalization
%%%
tag := "Chapter6/Example6.4.9/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.AdjInputSetCardinalities.set_from_adj_at_eight_finite_and_ncard_eq}

{Manual.docstring RepresentationTheory.AdjInputSetCardinalities.set_from_adj_at_seven_finite_and_ncard_eq}

{Manual.docstring RepresentationTheory.AdjInputSetCardinalities.set_from_adj_at_six_finite_and_ncard_eq}

{Manual.docstring RepresentationTheory.FiniteSetCardinality.finite_and_ncard_eq_mul_sub_one}

{Manual.docstring RepresentationTheory.IntegerZeroSumCoordinates.auxiliary_set_ncard}

{Manual.docstring RepresentationTheory.IntegerZeroSumCoordinates.mem_singleton_difference_set_iff}
