/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter4.Remark453

#doc (Manual) "Characters defined without representations via convolution algebra" =>

# Characters defined without representations via convolution algebra
%%%
tag := "Chapter4/Remark4.5.3"
number := false
%%%

**Remark 4.5.3.** We see that characters of irreducible complex representations of $`G` can be defined without mentioning irreducible representations. Namely, equip the space $`F(G, \mathbb{C})` of complex-valued functions on $`G` with the convolution product

$$`(f * g)(z) = \sum_{x, y \in G : xy = z} f(x)g(y).`

This product turns $`F(G, \mathbb{C})` into an associative algebra, with unit $`\delta_e` (the characteristic function of the unit $`e \in G`), and the space of class functions $`F_c(G, \mathbb{C})` is a commutative subalgebra. Then one can define renormalized characters $`\tilde{\chi}_i \in F_c(G, \mathbb{C})` to be the primitive idempotents in this algebra, i.e., solutions of the equation $`f * f = f` which cannot be decomposed into a sum of other nonzero solutions. Then one can define the characters by the formula

$$`\chi_i(g) = \sqrt{\frac{|G|}{\tilde{\chi}_i(1)}} \tilde{\chi}_i(g)`

(check it!). This is, essentially, how Frobenius defined characters (see \[**Cu**\], equation (7)). Note that Frobenius defined representations at approximately the same time, but for some time it was not clear that there is a simple relation between irreducible representations and characters (namely, that irreducible characters are simply traces of group elements in irreducible representations). Even today, many group theorists sometimes talk of irreducible characters of a finite group rather than irreducible representations.

## Formalization
%%%
tag := "Chapter4/Remark4.5.3/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.CharacterCoefficientAlgebra.auxiliaryComplexGroupSubalgebra}

{Manual.docstring RepresentationTheory.CharacterCoefficientAlgebra.auxiliaryRingElementPredicate_iff_exists_simple_representationElement}

{Manual.docstring RepresentationTheory.CharacterCoefficientAlgebra.character_eq_card_div_finrank_mul_coefficient}

### Supporting declarations

{Manual.docstring RepresentationTheory.CharacterCoefficientAlgebra.coeff_mul_eq_sum_coeff_mul_coeff_inv_mul}
