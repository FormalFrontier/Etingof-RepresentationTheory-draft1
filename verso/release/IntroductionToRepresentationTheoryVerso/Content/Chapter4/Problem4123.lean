/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter4.Problem4123

#doc (Manual) "Irreducibility of symmetric and exterior powers for GL(V)" =>

# Irreducibility of symmetric and exterior powers for GL(V)
%%%
tag := "Chapter4/Problem4.12.3"
number := false
%%%

**Problem 4.12.3.** Let $`V` be a finite dimensional complex vector space, and let $`GL(V)` be the group of invertible linear transformations of $`V`. Then $`S^n V` and $`\Lambda^m V` ($`m \leq \dim(V)`) are representations of $`GL(V)` in a natural way. Show that they are irreducible representations.

Hint: Choose a basis $`\{e_i\}` in $`V`. Find a diagonal element $`H` of $`GL(V)` such that $`\rho(H)` has distinct eigenvalues (where $`\rho` is one of the above representations). This shows that if $`W` is a subrepresentation, then it is spanned by a subset $`S` of a basis of eigenvectors of $`\rho(H)`. Use the invariance of $`W` under the operators $`\rho(1 + E_{ij})` (where $`E_{ij}` is defined by $`E_{ij} e_k = \delta_{jk} e_i`) for all $`i \neq j` to show that if the subset $`S` is nonempty, it is necessarily the entire basis.

## Formalization
%%%
tag := "Chapter4/Problem4.12.3/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.ExteriorSymmetricAuxiliary.exteriorPower_invariantSubmodule_eq_bot_or_top}

{Manual.docstring RepresentationTheory.LinearAlgebra.ExteriorPower.InvariantSubmodules.eq_bot_or_eq_top_of_exteriorPower_invariant}

{Manual.docstring RepresentationTheory.SymmetricPower.LinearAction.symmetricPower_submodule_bot_or_top_of_forall_linearEquiv_map_mem}

{Manual.docstring RepresentationTheory.SymmetricPower.LinearAction.symmetricPower_submodule_eq_bot_or_eq_top_of_forall_linearEquiv_map_mem}
