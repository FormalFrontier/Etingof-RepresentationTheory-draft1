/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Problem527

#doc (Manual) "Galois extension for representations and vanishing of characters" =>

# Galois extension for representations and vanishing of characters
%%%
tag := "Chapter5/Problem5.2.7"
number := false
%%%
**Problem 5.2.7.** (a) Show that for any finite group $`G` there exists a finite Galois extension $`K \subset \mathbb{C}` of $`\mathbb{Q}` such that any finite dimensional complex representation of $`G` has a basis in which the matrices of the group elements have entries in $`K`.

Hint: Consider the representations of $`G` over the field $`\overline{\mathbb{Q}}` of algebraic numbers.

(b) Show that if $`V` is an irreducible complex representation of a finite group $`G` of dimension $`> 1`, then there exists $`g \in G` such that $`\chi_V(g) = 0`.

Hint: Assume the contrary. Use orthonormality of characters to show that the arithmetic mean of the numbers $`|\chi_V(g)|^2` for $`g \neq 1` is $`< 1`. Deduce that their product $`\beta` satisfies $`0 < \beta < 1`. Show that all conjugates of $`\beta` satisfy the same inequalities (consider the Galois conjugates of the representation $`V`, i.e., representations obtained from $`V` by the action of the Galois group of $`K` over $`\mathbb{Q}` on the matrices of group elements in the basis from part (a)). Then derive a contradiction.

## Formalization
%%%
tag := "Chapter5/Problem5.2.7/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.FiniteGroup.RationalForms.FDRep.exists_character_eq_zero_of_simple}

{Manual.docstring RepresentationTheory.FiniteGroup.RationalForms.FDRep.exists_universal_finiteGalois_fieldOfDefinition}

### Supporting declarations

{Manual.docstring RepresentationTheory.FiniteGroup.RationalForms.FDRep.normSqCharacterProduct_mem_Ioo}
