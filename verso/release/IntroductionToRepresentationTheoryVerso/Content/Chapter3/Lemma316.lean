/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.Lemma316

#doc (Manual) "Surjective map from direct sum of irreducibles splits" =>
# Surjective map from direct sum of irreducibles splits
%%%
tag := "Chapter3/Lemma3.1.6"
number := false
%%%
**Lemma 3.1.6.** _There exists a subset $`J \subseteq I` such that $`V_J := \bigoplus_{i \in J} V_i` is mapped isomorphically by $`f` onto $`U`._

**Proof.** Let $`J` be a maximal subset such that $`f|_{V_J}` is injective. If $`f(V_J) \neq U`, then there exists $`i \in I` such that $`f(V_i)` is not contained in $`f(V_J)`. Then the map $`V_i \to U/f(V_J)` is nonzero, and hence injective by Schur's lemma. Let $`J' = J \cup \{i\}`; then $`f` is injective on $`V_{J'}`, contradicting the maximality of $`J`, which proves the lemma. $`\square`

## Formalization
%%%
tag := "Chapter3/Lemma3.1.6/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Module.ComplementConstructions.exists_isCompl_iSup_ker}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.Module.ComplementConstructions.disjoint_sup_of_disjoint}

{Manual.docstring RepresentationTheory.Algebra.Module.ComplementConstructions.exists_bijective_restriction_of_surjective}

{Manual.docstring RepresentationTheory.Algebra.Module.ComplementConstructions.exists_map_agreeing_on_iSup}

{Manual.docstring RepresentationTheory.Algebra.Module.ComplementConstructions.exists_map_agreeing_on_iSup_of_internal}
