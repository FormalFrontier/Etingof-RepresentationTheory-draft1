/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter7.DiscussionAfterDefinition781

#doc (Manual) "Morphisms of complexes, cocycles, coboundaries, bounded complexes" =>

# Morphisms of complexes, cocycles, coboundaries, bounded complexes
%%%
tag := "Chapter7/Discussion_after_Definition7.8.1"
number := false
%%%

There is an obvious notion of a *morphism of complexes*. Namely, a morphism $`f : C \to D` is a collection of morphisms $`f_i : C_i \to D_i` such that $`d_i \circ f_i = f_{i+1} \circ d_i`. Clearly, such morphisms can be composed, which makes the class of all complexes over $`\mathcal{C}` into a category, denoted $`\operatorname{Compl}(\mathcal{C})`.

In particular, one can consider complexes of abelian groups, vector spaces, modules over a ring, etc. In this case, elements of $`\operatorname{Ker}(d_i)` are called $`i`-*cocycles*, the elements of $`\operatorname{Im}(d_{i-1})` are called $`i`-*coboundaries*, and the elements of $`H^i(C)` are called $`i`th *cohomology classes*. This terminology is adopted from topology. For this reason, exact sequences are also called *acyclic complexes* (as they are complexes which have no nontrivial cocycles, i.e., cocycles that are not coboundaries).

Often one considers complexes that are bounded in one or both directions; i.e., the objects $`C_i` are zero for $`i \gg 0`, $`i \ll 0`, or both. In this case one writes one zero on each side where the complex is bounded. For example, a complex bounded on both sides with $`n + 1` terms will look like

$$`0 \to C_0 \to C_1 \to \cdots \to C_n \to 0.`
