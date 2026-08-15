/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.DiscussionAfterTheorem212

#doc (Manual) "Dynkin diagrams significance; representation theory of finite groups overview" =>
# Dynkin diagrams significance; representation theory of finite groups overview
%%%
tag := "Chapter2/Discussion_after_Theorem2.1.2"
number := false
%%%
As a final example consider the representation theory of finite groups, which is one of the most
fascinating chapters of representation theory. In this theory, one considers representations of
the group algebra $`A = \mathbb{C}[G]` of a finite group $`G` — the algebra with basis $`a_g`,
$`g \in G`, and multiplication law $`a_g a_h = a_{gh}`. We will show that any finite dimensional
representation of $`A` is a direct sum of irreducible representations, i.e., the notions of an
irreducible and indecomposable representation are the same for $`A` (Maschke's theorem). Another
striking result discussed below is the Frobenius divisibility theorem: the dimension of any
irreducible representation of $`A` divides the order of $`G`. Finally, we will show how to use the
representation theory of finite groups to prove Burnside's theorem: any finite group of order
$`p^a q^b`, where $`p, q` are primes, is solvable. Note that this theorem does not mention
representations, which are used only in its proof; a purely group-theoretical proof of this
theorem (not using representations) exists but is much more difficult!

## Formalization
%%%
tag := "Chapter2/Discussion_after_Theorem2.1.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Module.AuxiliaryPredicates.Module.isSimpleModule_of_auxiliaryPredicate}

{Manual.docstring RepresentationTheory.FiniteGroupSolvability.isSolvable_of_card_eq_prime_pow_mul_prime_pow}

{Manual.docstring RepresentationTheory.LinearAlgebra.ModuleDecompositions.AuxiliaryDecompositionPredicate.of_isSimpleModule}

### Supporting declarations

{Manual.docstring RepresentationTheory.FiniteGroup.RegularRepresentationDecomposition.MonoidAlgebra.isSemisimpleRing_of_isUnit_card}
