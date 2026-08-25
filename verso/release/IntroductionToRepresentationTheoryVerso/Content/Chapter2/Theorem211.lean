/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Theorem211

#doc (Manual) "Classification of irreducible representations of U(sl(2))" =>
# Classification of irreducible representations of U(sl(2))
%%%
tag := "Chapter2/Theorem2.1.1"
number := false
%%%
*Theorem 2.1.1.* _Let $`k = \mathbb{C}` be the field of complex numbers. Then:_

_(i) The algebra $`U` has exactly one irreducible representation $`V_d` of each dimension, up to equivalence; this representation is realized in the space of homogeneous polynomials of two variables $`x, y` of degree $`d - 1` and is defined by the formulas_

$$`\rho(h) = x\frac{\partial}{\partial x} - y\frac{\partial}{\partial y}, \quad \rho(e) = x\frac{\partial}{\partial y}, \quad \rho(f) = y\frac{\partial}{\partial x}.`

_(ii) Any indecomposable finite dimensional representation of $`U` is irreducible. That is, any finite dimensional representation of $`U` is a direct sum of irreducible representations._

## Formalization
%%%
tag := "Chapter2/Theorem2.1.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.LieAlgebra.FiniteDimensionalModules.exists_irreducible_of_finrank}

{Manual.docstring RepresentationTheory.LieAlgebra.FiniteDimensionalModules.isIrreducible_of_auxiliaryLieModuleCondition}

{Manual.docstring RepresentationTheory.LieAlgebra.FiniteDimensionalModules.lieHomEquivEnvelopingAlgHom}

{Manual.docstring RepresentationTheory.LieAlgebra.FiniteDimensionalModules.nonempty_equiv_of_irreducible_finrank_eq}

### Supporting declarations

{Manual.docstring RepresentationTheory.LieAlgebra.FiniteDimensionalModules.exists_polynomial_model}

{Manual.docstring RepresentationTheory.LieAlgebra.FiniteDimensionalModules.intertwines_iff_enveloping_intertwines}

{Manual.docstring RepresentationTheory.LieAlgebra.FiniteDimensionalModules.invariant_iff_enveloping_invariant}

{Manual.docstring RepresentationTheory.LieAlgebra.FiniteDimensionalModules.lieSubmodule_complementedLattice}

{Manual.docstring RepresentationTheory.LieAlgebra.MatrixSubalgebraRepresentationAuxiliary.finFunction_isIrreducible}
