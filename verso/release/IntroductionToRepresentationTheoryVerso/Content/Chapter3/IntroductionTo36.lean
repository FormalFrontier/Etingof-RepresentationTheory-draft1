/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.IntroductionTo36

#doc (Manual) "Section 3.6: Characters of representations \u2014 heading and character definition" =>
# Section 3.6: Characters of representations — heading and character definition
%%%
tag := "Chapter3/Introduction_to_3.6"
number := false
%%%

## 3.6. Characters of representations
%%%
tag := "Chapter3/Introduction_to_3.6/heading-1"
%%%

Let $`A` be an algebra and $`V` a finite dimensional representation of $`A` with action $`\rho`. Then the **character** of $`V` is the linear function $`\chi_V : A \to k` given by

$$`\chi_V(a) = \operatorname{Tr}|_V(\rho(a)).`

If $`[A, A]` is the span of commutators $`[x, y] := xy - yx` over all $`x, y \in A`, then $`[A, A] \subseteq \ker \chi_V`. Thus, we may view the character as a mapping $`\chi_V : A/[A, A] \to k`.

## Formalization
%%%
tag := "Chapter3/Introduction_to_3.6/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Module.AuxiliaryQuotientMap.auxiliarySubmodule_le_ker}

{Manual.docstring RepresentationTheory.Algebra.Module.AuxiliaryQuotientMap.linearMapOnAuxiliaryQuotient}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.Module.AuxiliaryQuotientMap.auxiliaryLinearMap_mul_comm}

{Manual.docstring RepresentationTheory.Algebra.Module.AuxiliaryQuotientMap.auxiliarySubmodule}

{Manual.docstring RepresentationTheory.Algebra.Module.AuxiliaryQuotientMap.linearMapOnAuxiliaryQuotient_mk}

{Manual.docstring RepresentationTheory.Algebra.Module.Dual.SimpleFamilies.moduleDualElement}
