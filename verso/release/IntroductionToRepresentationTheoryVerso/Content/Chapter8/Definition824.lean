/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter8.Definition824

#doc (Manual) "Ext functors" =>

# Ext functors
%%%
tag := "Chapter8/Definition8.2.4"
number := false
%%%

*Definition 8.2.4.* Let $`M` be a left $`A`-module, $`P_\bullet` a projective resolution of $`M`, and $`N` a left $`A`-module. For $`i \geq 0` we define $`\mathrm{Ext}^i_A(M, N) = \mathrm{Ext}^i(M, N)` to be the $`i`th cohomology of the complex

$$`0 \to \mathrm{Hom}_A(P_0, N) \to \mathrm{Hom}_A(P_1, N) \to \mathrm{Hom}_A(P_2, N) \to \ldots`

induced by the resolution $`P_\bullet`.

## Formalization
%%%
tag := "Chapter8/Definition8.2.4/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses}
