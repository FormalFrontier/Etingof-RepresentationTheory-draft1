/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter6.Remark6411

#doc (Manual) "Remark 6.4.11: Weyl group" =>

# Remark 6.4.11: Weyl group
%%%
tag := "Chapter6/Remark6.4.11"
number := false
%%%

*Remark 6.4.11.* As a linear operator of $`\mathbb{R}^n`, $`s_\alpha` fixes any vector orthogonal to $`\alpha` and

$$`s_\alpha(\alpha) = -\alpha.`

Therefore $`s_\alpha` is the reflection at the hyperplane orthogonal to $`\alpha` and in particular fixes $`B`. The $`s_i := s_{\alpha_i}` generate a subgroup $`W \subseteq O(\mathbb{R}^n)`, which is called *the Weyl group* of $`\Gamma`. Since for every $`w \in W`, $`w(\alpha_i)` is a root, and since there are only finitely many roots, $`W` has to be finite.

## Formalization
%%%
tag := "Chapter6/Remark6.4.11/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.LinearAlgebra.IntegralRootSystem.WeylGroup.IntegralRootSystem.finite_weylGroup}

{Manual.docstring RepresentationTheory.LinearAlgebra.IntegralRootSystem.WeylGroup.IntegralRootSystem.weylGroupRootAction_injective}

### Supporting declarations

{Manual.docstring RepresentationTheory.LinearAlgebra.IntegralRootSystem.WeylGroup.IntegralRootSystem.reflection_eq_self_of_dotProduct_eq_zero}

{Manual.docstring RepresentationTheory.LinearAlgebra.IntegralRootSystem.WeylGroup.IntegralRootSystem.reflection_preserves_dotProduct_mulVec}

{Manual.docstring RepresentationTheory.LinearAlgebra.IntegralRootSystem.WeylGroup.IntegralRootSystem.reflection_self}
