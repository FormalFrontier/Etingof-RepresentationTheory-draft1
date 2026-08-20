/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter8.Theorem811

#doc (Manual) "Equivalent characterizations of projective modules" =>

# Equivalent characterizations of projective modules
%%%
tag := "Chapter8/Theorem8.1.1"
number := false
%%%

*Theorem 8.1.1.* _The following properties of $`P` are equivalent:_

_(i) If $`\alpha : M \to N` is a surjective morphism and $`\nu : P \to N` is any morphism, then there exists a morphism $`\mu : P \to M` such that $`\alpha \circ \mu = \nu`._

_(ii) Any surjective morphism $`\alpha : M \to P` splits; i.e., there exists $`\mu : P \to M` such that $`\alpha \circ \mu = \operatorname{id}`._

_(iii) There exists another $`A`-module $`Q` such that $`P \oplus Q` is a free $`A`-module, i.e., a direct sum of copies of $`A`._

_(iv) The functor $`\operatorname{Hom}_A(P, ?)` on the category of $`A`-modules is exact._

*Proof.* To prove that (i) implies (ii), take $`N = P`. To prove that (ii) implies (iii), take $`M` to be free (this can always be done since any module is a quotient of a free module). To prove that (iii) implies (iv), note that the functor $`\operatorname{Hom}_A(P, ?)` is exact if $`P` is free (as
$`\operatorname{Hom}_A(A, N) = N`), so the statement follows, since if the direct sum of two complexes is exact, then each of them is exact. To prove that (iv) implies (i), let $`K` be the kernel of the map $`\alpha`, and apply the exact functor $`\operatorname{Hom}_A(P, ?)` to the exact sequence

$$`0 \to K \to M \to N \to 0.`

$`\square`

## Formalization
%%%
tag := "Chapter8/Theorem8.1.1/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.Mathlib.LinearAlgebra.Projective.Module.Projective.iff_exists_retract}

{Manual.docstring RepresentationTheory.Mathlib.LinearAlgebra.Projective.Module.Projective.iff_hom_preserves_short_exact}

{Manual.docstring RepresentationTheory.Mathlib.LinearAlgebra.Projective.Module.Projective.iff_surjective_splits}
