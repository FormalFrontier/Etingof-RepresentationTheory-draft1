/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Problem274

#doc (Manual) "Representations and ideals of the Weyl algebra" =>
# Representations and ideals of the Weyl algebra
%%%
tag := "Chapter2/Problem2.7.4"
number := false
%%%
**Problem 2.7.4.** Let $`A` be the Weyl algebra.

(a) If $`\operatorname{char} k = 0`, what are the finite dimensional representations of $`A`? What are the two-sided ideals in $`A`?

Hint: For the first question, use the fact that for two square matrices $`B, C`, $`\operatorname{Tr}(BC) = \operatorname{Tr}(CB)`. For the second question, show that any nonzero two-sided ideal in $`A` contains a nonzero polynomial in $`x`, and use this to characterize this ideal.

Suppose for the rest of the problem that $`\operatorname{char} k = p`.
(b) What is the center of $`A`?

Hint: Show that $`x^p` and $`y^p` are central elements.

(c) Find all irreducible finite dimensional representations of $`A`.

Hint: Let $`V` be an irreducible finite dimensional representation of $`A`, and let $`v` be an eigenvector of $`y` in $`V`. Show that the collection of vectors $`\{v, xv, x^2 v, \ldots, x^{p-1} v\}` is a basis of $`V`.

## Formalization
%%%
tag := "Chapter2/Problem2.7.4/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.NoncommutativeAlgebra.PositiveCharacteristic.center_eq_adjoin_powers}

{Manual.docstring RepresentationTheory.NoncommutativeAlgebra.PositiveCharacteristic.finrank_eq_zero_of_charZero}

{Manual.docstring RepresentationTheory.NoncommutativeAlgebra.PositiveCharacteristic.isSimpleRing_of_charZero}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.PrimeCharacteristicCyclicModels.existsUnique_nonempty_moduleScalarParameterType}

{Manual.docstring RepresentationTheory.Algebra.PrimeCharacteristicCyclicModels.exists_nonempty_moduleScalarParameterType}

{Manual.docstring RepresentationTheory.Algebra.PrimeCharacteristicCyclicModels.finrank_finFunction}

{Manual.docstring RepresentationTheory.Algebra.PrimeCharacteristicCyclicModels.modelModule_isSimpleModule}

{Manual.docstring RepresentationTheory.Algebra.PrimeCharacteristicCyclicModels.nonempty_fourScalarParameterType_iff}

{Manual.docstring RepresentationTheory.NoncommutativeAlgebra.PositiveCharacteristic.exists_cyclic_basis_of_simpleModule}

{Manual.docstring RepresentationTheory.NoncommutativeAlgebra.PositiveCharacteristic.power_firstGenerator_mem_center}

{Manual.docstring RepresentationTheory.NoncommutativeAlgebra.PositiveCharacteristic.power_secondGenerator_mem_center}
