/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso Genre

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Definition237

#doc (Manual) "Direct sum of representations" =>
# Direct sum of representations
%%%
tag := "Chapter2/Definition2.3.7"
number := false
%%%
*Definition 2.3.7.* Let $`V_1, V_2` be representations of an algebra $`A`. Then the space $`V_1 \oplus V_2` has an obvious structure of a representation of $`A`, given by $`a(v_1 \oplus v_2) = av_1 \oplus av_2`. This representation is called the *direct sum* of $`V_1` and $`V_2`.

## Formalization
%%%
tag := "Chapter2/Definition2.3.7/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.LinearAlgebra.ProductModules.smul_prod_mk}

### Supporting declarations

{Manual.docstring RepresentationTheory.LinearAlgebra.ProductModules.AuxiliaryBinaryTypeConstructor}
