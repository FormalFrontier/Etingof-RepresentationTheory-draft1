/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter8.Theorem815

#doc (Manual) "Equivalent characterizations of injective modules" =>

# Equivalent characterizations of injective modules
%%%
tag := "Chapter8/Theorem8.1.5"
number := false
%%%

*Theorem 8.1.5.* _The following properties of $`I` are equivalent:_

_(i) If $`\alpha : N \to M` is an injective morphism and $`\nu : N \to I` is any morphism, then there exists a morphism $`\mu : M \to I` such that $`\mu \circ \alpha = \nu`._

_(ii) Any injective morphism $`\alpha : I \to M` splits; i.e., there exists $`\mu : M \to I` such that $`\mu \circ \alpha = \operatorname{id}`._
_(iii) The functor $`\operatorname{Hom}_A(?, I)` on the category of A-modules is exact._

*Proof.* The proof of the implications "(i) implies (ii)" and "(iii) implies (i)" is similar to the proof of Theorem 8.1.1. Let us prove that (ii) implies (iii). Let

$$`
0 \to N \to M \to K \to 0
`

be an exact sequence. Denote the embedding $`N \to M` by $`j`. Consider the corresponding sequence

$$`
0 \to \operatorname{Hom}(K, I) \to \operatorname{Hom}(M, I) \to \operatorname{Hom}(N, I) \to 0.
`

Let $`f \in \operatorname{Hom}(N, I)`, and define the module $`E := (M \oplus I)/N`, where $`N` is embedded into $`M \oplus I` via $`x \mapsto (j(x), -f(x))`. Clearly, we have an inclusion $`I \to E`, since the image of $`N \oplus I` in $`E` is naturally identified with $`I`. So there is a splitting $`E \to I` of this inclusion, i.e., a map $`M \oplus I \to I`, $`(m, i) \mapsto g(m) + i` such that $`g(j(x)) - f(x) = 0`. This means that the map $`j^* : \operatorname{Hom}(M, I) \to \operatorname{Hom}(N, I)` is surjective, i.e., the functor $`\operatorname{Hom}(?, I)` is exact, as desired. $`\square`

## Formalization
%%%
tag := "Chapter8/Theorem8.1.5/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Mathlib.LinearAlgebra.Injective.Module.injective_iff_every_injective_map_from_splits}

{Manual.docstring RepresentationTheory.Mathlib.LinearAlgebra.Injective.Module.injective_iff_hom_exact_on_short_exact}
