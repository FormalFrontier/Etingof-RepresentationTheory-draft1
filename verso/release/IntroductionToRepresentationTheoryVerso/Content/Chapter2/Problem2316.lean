/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Problem2316

#doc (Manual) "Central character of representations" =>
# Central character of representations
%%%
tag := "Chapter2/Problem2.3.16"
number := false
%%%
**Problem 2.3.16.** Let $`A` be an algebra over a field $`k`. The center $`Z(A)` of $`A` is the set of all elements $`z \in A` which commute with all elements of $`A`. For example, if $`A` is commutative, then $`Z(A) = A`.

(a) Show that if $`V` is an irreducible finite dimensional representation of $`A`, then any element $`z \in Z(A)` acts in $`V` by multiplication by some scalar $`\chi_V(z)`. Show that $`\chi_V : Z(A) \to k` is a homomorphism. It is called the **central character** of $`V`.

(b) Show that if $`V` is an indecomposable finite dimensional representation of $`A`, then for any $`z \in Z(A)`, the operator $`\rho(z)` by which $`z` acts in $`V` has only one eigenvalue $`\chi_V(z)`, equal to the scalar by which $`z` acts on some irreducible subrepresentation of $`V`. Thus $`\chi_V : Z(A) \to k` is a homomorphism, which is again called the central character of $`V`.

(c) Does $`\rho(z)` in (b) have to be a scalar operator?

## Formalization
%%%
tag := "Chapter2/Problem2.3.16/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.CenterAction.centerAction_eq_character_smul}

{Manual.docstring RepresentationTheory.Algebra.CenterAction.centerCharacter}

{Manual.docstring RepresentationTheory.Algebra.CenterAction.centerElement_smul_eq_scalar_smul}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.CenterAction.centerAction_sub_scalar_isNilpotent}

{Manual.docstring RepresentationTheory.Algebra.CenterAction.centerCharacter_value_unique}

{Manual.docstring RepresentationTheory.Algebra.CenterAction.dualNumberEpsilon_not_scalarAction}

{Manual.docstring RepresentationTheory.Algebra.CenterAction.exists_simpleSubmodule_centerCharacter}
