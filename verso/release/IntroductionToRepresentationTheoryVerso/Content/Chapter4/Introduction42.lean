/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter4.Introduction42

#doc (Manual) "Section 4.2: Characters" =>

# Section 4.2: Characters
%%%
tag := "Chapter4/Introduction_4.2"
number := false
%%%

## 4.2. Characters
%%%
tag := "Chapter4/Introduction_4.2/heading-1"
%%%

If $`V` is a finite dimensional representation of a finite group $`G`, then its character $`\chi_V : G \to k` is defined by the formula $`\chi_V(g) = \operatorname{Tr}|_V(\rho(g))`. Obviously, $`\chi_V(g)` is simply the restriction of the character $`\chi_V(a)` of $`V` as a representation of the algebra $`A = k[G]` to the basis $`G \subset A`, so it carries exactly the same information. The character is a **central function**, or **class function**: $`\chi_V(g)` depends only on the conjugacy class of $`g`; i.e., $`\chi_V(hgh^{-1}) = \chi_V(g)`.

Denote by $`F(G, k)` the space of $`k`-valued functions on $`G` and by $`F_c(G, k) \subset F(G, k)` the subspace of class functions.

## Formalization
%%%
tag := "Chapter4/Introduction_4.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.ConjugationInvariantCharacters.character_eq_auxiliaryMap_apply}

{Manual.docstring RepresentationTheory.ConjugationInvariantCharacters.mem_conjugationInvariantSubmodule_iff}

### Supporting declarations

{Manual.docstring RepresentationTheory.ConjugationInvariantCharacters.AuxiliaryFunctionSpace}

{Manual.docstring RepresentationTheory.ConjugationInvariantCharacters.character_mem_conjugationInvariantSubmodule}

{Manual.docstring RepresentationTheory.ConjugationInvariantCharacters.conjugationInvariantSubmodule}
