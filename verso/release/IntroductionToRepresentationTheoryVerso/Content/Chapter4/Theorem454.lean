/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter4.Theorem454

#doc (Manual) "Column orthogonality of characters" =>

# Column orthogonality of characters
%%%
tag := "Chapter4/Theorem4.5.4"
number := false
%%%

**Theorem 4.5.4.** _Let $`g, h \in G`, and let $`Z_g` denote the centralizer of $`g` in $`G`. Then_

$$`\sum_V \chi_V(g)\overline{\chi_V(h)} = \begin{cases} |Z_g|, & \text{if } g \text{ is conjugate to } h, \\ 0, & \text{otherwise,} \end{cases}`

_where the summation is taken over all irreducible representations of $`G`._

**Proof.** As noted above, $`\overline{\chi_V(h)} = \chi_{V^*}(h)`, so the left-hand side equals (using Maschke's theorem):

$$`\sum_V \chi_V(g)\chi_{V^*}(h) = \operatorname{Tr}|_{\bigoplus_V V \otimes V^*}(g \otimes (h^*)^{-1})`

$$`= \operatorname{Tr}|_{\bigoplus_V \operatorname{End} V}(x \mapsto gxh^{-1}) = \operatorname{Tr}|_{\mathbb{C}[G]}(x \mapsto gxh^{-1}).`

## Formalization
%%%
tag := "Chapter4/Theorem4.5.4/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.FiniteGroup.CharacterColumnOrthogonality.FiniteGroup.sum_complete_simple_characters_mul_inv}
