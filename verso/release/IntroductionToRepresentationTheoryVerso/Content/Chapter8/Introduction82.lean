/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter8.Introduction82

#doc (Manual) "Section 8.2: Tor and Ext functors" =>

# Section 8.2: Tor and Ext functors
%%%
tag := "Chapter8/Introduction_8.2"
number := false
%%%

## 8.2. Tor and Ext functors
%%%
tag := "Chapter8/Introduction_8.2/heading-1"
%%%

Let $`A` be a unital ring. As we have mentioned in Example 7.9.6, the functors $`M \otimes_A ?` and $`\operatorname{Hom}_A(M, ?)` (where $`M` is a right, respectively
left, $`A`-module) on the category of left $`A`-modules are, in general, not exact (they are only exact on one side). The job of the functors $`\mathrm{Tor}_i^A(M, ?)` and $`\mathrm{Ext}^i_A(M, ?)` is to quantify the extent to which the functors $`M \otimes_A ?` and $`\mathrm{Hom}_A(M, ?)` fail to be exact. Namely, these functors are defined as follows.

## Formalization
%%%
tag := "Chapter8/Introduction_8.2/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.CategoryTheory.Abelian.ExtensionClasses.CategoryTheory.ExtensionClasses}
