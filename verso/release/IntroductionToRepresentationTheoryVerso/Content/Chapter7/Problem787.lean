/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter7.Problem787

#doc (Manual) "Tensor product of complexes and K\u00fcnneth formula" =>

# Tensor product of complexes and Künneth formula
%%%
tag := "Chapter7/Problem7.8.7"
number := false
%%%

*Problem 7.8.7.* Let $`C_\bullet` and $`D_\bullet` be complexes of modules over a commutative ring $`A`. Define the tensor product complex $`(C \otimes D)_\bullet` by the formula

$$`
(C \otimes D)_i = \bigoplus_{j+m=i} C_j \otimes_A D_m,
`

with differentials

$$`
d_i^{C \otimes D}|_{C_j \otimes D_m} = d_j^C \otimes 1 + (-1)^j \cdot 1 \otimes d_m^D.
`
(i) Show that this is a complex.

Now assume that $`A = k` is a field.

(ii) Show that if $`C` or $`D` is an exact sequence, then so is $`C \otimes D`.

Hint: Use the decomposition of Exercise 7.8.4.

(iii) Show that any complex $`C` can be identified with a direct sum of an exact sequence and the complex consisting of $`H^i(C)` with the zero differentials, in such a way that the induced isomorphism $`H^i(C) \to H^i(C)` is the identity.

(iv) Show that there is a natural isomorphism of vector spaces

$$`
H^i(C \otimes D) \cong \bigoplus_{j+m=i} H^j(C) \otimes H^m(D).
`

This is the *Künneth* formula.

## Formalization
%%%
tag := "Chapter7/Problem7.8.7/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Homology.CochainComplex.HomologyComplex.tensorProduct_acyclic_of_acyclic}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.Homology.CochainComplex.HomologyComplex.exists_biprod_inr_comp_iso_inv_homologyMap_isIso}

{Manual.docstring RepresentationTheory.Algebra.Homology.CochainComplex.HomologyComplex.tensorProduct_d_comp_d}

{Manual.docstring RepresentationTheory.HomologicalComplex.TensorHomology.homologyTensorToSigmaIso}

{Manual.docstring RepresentationTheory.HomologicalComplex.TensorHomology.tensorHomologyFunctorIso}
