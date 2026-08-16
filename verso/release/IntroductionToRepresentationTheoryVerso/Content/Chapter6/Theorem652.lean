/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter6.Theorem652

#doc (Manual) "Theorem 6.5.2: Gabriel's theorem" =>

# Theorem 6.5.2: Gabriel's theorem
%%%
tag := "Chapter6/Theorem6.5.2"
number := false
%%%

*Theorem 6.5.2* (Gabriel's theorem). _Let $`Q` be a quiver of type $`A_n`, $`D_n`, $`E_6`, $`E_7`, $`E_8`. Then $`Q` has finitely many indecomposable representations. Namely, the dimension vector of any indecomposable representation is a positive root (with respect to $`B_\Gamma`) and for any positive root $`\alpha` there is exactly one indecomposable representation with dimension vector $`\alpha`._

## Formalization
%%%
tag := "Chapter6/Theorem6.5.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Quiver.DimensionVectorClassification.Quiver.exists_finrankVector_and_related_of_vectorPredicate}

{Manual.docstring RepresentationTheory.Quiver.DimensionVectorClassification.Quiver.finite_and_finrankVector_classification}

### Supporting declarations

{Manual.docstring RepresentationTheory.Quiver.DimensionVectorClassification.finite_setOf_vectorPredicate}

{Manual.docstring RepresentationTheory.Quiver.DimensionVectorClassification.vectorPredicate_of_nonneg_of_dot_mulVec_eq_two}
