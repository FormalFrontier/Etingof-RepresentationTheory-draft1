/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter4.Remark455

#doc (Manual) "Unitary matrix proof of column orthogonality" =>

# Unitary matrix proof of column orthogonality
%%%
tag := "Chapter4/Remark4.5.5"
number := false
%%%

If $`g` and $`h` are not conjugate, this trace is clearly zero, since the matrix of the operator $`x \mapsto gxh^{-1}` in the basis of group elements has zero diagonal entries. On the other hand, if $`g` and $`h` are in the same conjugacy class, the trace is equal to the number of elements $`x` such that $`x = gxh^{-1}`, i.e., the order of the centralizer $`Z_g` of $`g`. We are done. $`\square`

**Remark 4.5.5.** Another proof of this result is as follows. Consider the matrix $`U` whose rows are labeled by irreducible representations of $`G` and whose columns are labeled by conjugacy classes, with entries $`U_{V,g} = \chi_V(g)/\sqrt{|Z_g|}`. Note that the conjugacy class of $`g` is $`G/Z_g`; thus $`|G|/|Z_g|` is the number of elements conjugate to $`g`. Thus, by Theorem 4.5.1, the rows of the matrix $`U` are orthonormal. This means that $`U` is unitary and hence its columns are also orthonormal, which implies the statement.

## Formalization
%%%
tag := "Chapter4/Remark4.5.5/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.ConjugacyClassCharacterMatrix.auxiliaryConjugacyClassMatrix_mul_conjTranspose_eq_one}

{Manual.docstring RepresentationTheory.ConjugacyClassCharacterMatrix.conjTranspose_auxiliaryConjugacyClassMatrix_mul_eq_one}

{Manual.docstring RepresentationTheory.ConjugacyClassCharacterMatrix.sum_character_inv_mul_character}
