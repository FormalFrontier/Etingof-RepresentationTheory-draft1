/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso Genre

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Definition236

#doc (Manual) "Homomorphism (intertwining operator) of representations" =>
# Homomorphism (intertwining operator) of representations
%%%
tag := "Chapter2/Definition2.3.6"
number := false
%%%
*Definition 2.3.6.* Let $`V_1, V_2` be two representations of an algebra $`A`. A *homomorphism* (or *intertwining operator*) $`\phi : V_1 \to V_2` is a linear operator which commutes with the action of $`A`, i.e., $`\phi(av) = a\phi(v)` for any $`v \in V_1`. A homomorphism $`\phi` is said to be an *isomorphism of representations* if it is an isomorphism of vector spaces. The set (space) of all homomorphisms of representations $`V_1 \to V_2` is denoted by $`\operatorname{Hom}_A(V_1, V_2)`.

Note that if a linear operator $`\phi : V_1 \to V_2` is an isomorphism of representations, then so is the linear operator $`\phi^{-1} : V_2 \to V_1` (check it!).

Two representations between which there exists an isomorphism are said to be isomorphic. For practical purposes, two isomorphic representations may be regarded as "the same", although there could be subtleties related to the fact that an isomorphism between two representations, when it exists, is not unique.

## Formalization
%%%
tag := "Chapter2/Definition2.3.6/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.LinearAlgebra.ModulePairAuxiliaries.AuxiliaryModulePairPredicate}

{Manual.docstring RepresentationTheory.LinearAlgebra.ModulePairAuxiliaries.ModulePairAuxiliary}

{Manual.docstring RepresentationTheory.LinearAlgebra.ModulePairAuxiliaries.ModulePairAuxiliary'}
