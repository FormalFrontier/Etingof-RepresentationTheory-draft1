/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Proposition5191

#doc (Manual) "Image of GL(V) in End(V^\\{\u2297n\\}) spans B" =>

# Image of GL(V) in End(V^\{⊗n\}) spans B
%%%
tag := "Chapter5/Proposition5.19.1"
number := false
%%%

*Proposition 5.19.1.* _The image of $`GL(V)` in $`\operatorname{End}(V^{\otimes n})` spans $`B`._

*Proof.* Recall that $`B` is spanned by the elements $`g^{\otimes n}`, $`g \in \operatorname{End} V`. Denote the span of $`g^{\otimes n}`, $`g \in GL(V)`, by $`B'`. Let $`b \in \operatorname{End} V` be any element.

We claim that $`B'` contains $`b^{\otimes n}`. Indeed, for all values of $`t` but finitely many, $`t \cdot \operatorname{Id} + b` is invertible, so $`(t \cdot \operatorname{Id} + b)^{\otimes n}` belongs to $`B'`. This implies that this is true for all $`t`, in particular $`t = 0`, since $`(t \cdot \operatorname{Id} + b)^{\otimes n}` is a polynomial of $`t`. More precisely, if $`f` is a linear function on $`\operatorname{End}(V^{\otimes n})` that vanishes on $`B'` then $`f((t \cdot \operatorname{Id} + b)^{\otimes n})` is a scalar-valued polynomial of $`t` which vanishes for almost all $`t \in k`, hence is identically zero.

The rest follows from Lemma 5.18.3. $`\square`

## Formalization
%%%
tag := "Chapter5/Proposition5.19.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.PiTensorProduct.MapSpanCentralizer.span_range_piTensorProduct_map_eq_auxiliary}

{Manual.docstring RepresentationTheory.PiTensorProduct.MapSpanCentralizer.span_range_piTensorProduct_map_eq_centralizer_auxiliary}
