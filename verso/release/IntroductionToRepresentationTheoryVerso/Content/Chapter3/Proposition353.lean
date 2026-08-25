/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.Proposition353

#doc (Manual) "Rad(A) is the largest nilpotent two-sided ideal" =>
# Rad(A) is the largest nilpotent two-sided ideal
%%%
tag := "Chapter3/Proposition3.5.3"
number := false
%%%
**Proposition 3.5.3.** _Let $`A` be a finite dimensional algebra._

_(i) Let $`I` be a nilpotent two-sided ideal in $`A`; i.e., $`I^n = 0` for some $`n`. Then $`I \subset \operatorname{Rad}(A)`._

_(ii) $`\operatorname{Rad}(A)` is a nilpotent ideal. Thus, $`\operatorname{Rad}(A)` is the largest nilpotent two-sided ideal in $`A`._
**Proof.** (i) Let $`V` be an irreducible representation of $`A`. Let $`v \in V`. Then $`Iv \subset V` is a subrepresentation. If $`Iv \neq 0`, then $`Iv = V` so there is $`x \in I` such that $`xv = v`. Then $`x^n \neq 0`, a contradiction. Thus $`Iv = 0`, so $`I` acts by $`0` in $`V` and hence $`I \subset \operatorname{Rad}(A)`.

(ii) Let $`0 = A_0 \subset A_1 \subset \cdots \subset A_n = A` be a filtration of the regular representation of $`A` by subrepresentations such that $`A_{i+1}/A_i` are irreducible. It exists by Lemma 3.4.2. Let $`x \in \operatorname{Rad}(A)`. Then $`x` acts on $`A_{i+1}/A_i` by zero, so $`x` maps $`A_{i+1}` to $`A_i`. This implies that $`\operatorname{Rad}(A)^n = 0`, as desired. $`\square`

## Formalization
%%%
tag := "Chapter3/Proposition3.5.3/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.RingTheory.JacobsonRadical.Nilpotence.jacobson_isNilpotent_of_finiteDimensional}

{Manual.docstring RepresentationTheory.RingTheory.JacobsonRadical.Nilpotence.nilpotent_le_jacobson}

### Supporting declarations

{Manual.docstring RepresentationTheory.RingTheory.JacobsonRadical.TwoSided.jacobson_isTwoSided}
