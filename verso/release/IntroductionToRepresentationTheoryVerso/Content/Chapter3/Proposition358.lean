/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.Proposition358

#doc (Manual) "Equivalent characterizations of semisimple algebras" =>
# Equivalent characterizations of semisimple algebras
%%%
tag := "Chapter3/Proposition3.5.8"
number := false
%%%
**Proposition 3.5.8.** _For a finite dimensional algebra $`A`, the following are equivalent:_

_(1) $`A` is semisimple._

_(2) $`\sum_i (\dim V_i)^2 = \dim A`, where the $`V_i`'s are the irreducible representations of $`A`._

_(3) $`A \cong \bigoplus_i \operatorname{Mat}_{d_i}(k)` for some $`d_i`._

_(4) Any finite dimensional representation of $`A` is completely reducible (that is, isomorphic to a direct sum of irreducible representations)._

_(5) $`A` is a completely reducible representation of $`A`._

**Proof.** As $`\dim A - \dim \operatorname{Rad}(A) = \sum_i (\dim V_i)^2`, clearly $`\dim A = \sum_i (\dim V_i)^2` if and only if $`\operatorname{Rad}(A) = 0`. Thus, $`(1) \Leftrightarrow (2)`.

By Theorem 3.5.4, if $`\operatorname{Rad}(A) = 0`, then clearly $`A \cong \bigoplus_i \operatorname{Mat}_{d_i}(k)` for $`d_i = \dim V_i`. Thus, $`(1) \Rightarrow (3)`.

Next, $`(3) \Rightarrow (4)` by Theorem 3.3.1. Clearly $`(4) \Rightarrow (5)`.

To see that $`(5) \Rightarrow (1)`, note that if $`A` is a completely reducible representation of $`A`, then each element of $`\operatorname{Rad}(A)` kills it, but the only element that kills $`1 \in A` is $`0`; thus $`\operatorname{Rad}(A) = 0`, so $`A` is semisimple. $`\square`

## Formalization
%%%
tag := "Chapter3/Proposition3.5.8/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Semisimplicity.FiniteDimensional.auxiliaryProperty_of_subsingleton}

{Manual.docstring RepresentationTheory.Algebra.Semisimplicity.FiniteDimensional.finiteDimensional_tfae}

{Manual.docstring RepresentationTheory.Algebra.Semisimplicity.FiniteDimensional.nonempty_algEquiv_finZero_matrix}

{Manual.docstring RepresentationTheory.Algebra.Semisimplicity.FiniteDimensional.not_auxiliaryProperty_of_subsingleton}

{Manual.docstring RepresentationTheory.Algebra.Semisimplicity.FiniteDimensional.not_isSimpleModule_of_subsingleton}

{Manual.docstring RepresentationTheory.Algebra.Semisimplicity.FiniteDimensional.not_isSimpleRing_of_subsingleton}

{Manual.docstring RepresentationTheory.Algebra.Semisimplicity.FiniteDimensional.subsingleton_module_of_subsingleton_ring}
