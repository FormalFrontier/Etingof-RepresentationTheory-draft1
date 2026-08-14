/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter9.Problem942

#doc (Manual) "Properties of projective dimension" =>

# Properties of projective dimension
%%%
tag := "Chapter9/Problem9.4.2"
number := false
%%%

*Problem 9.4.2.* (i) Show that $`\operatorname{pd}(M) \leq d` if and only if for any left $`A`-module $`N`, one has $`\operatorname{Ext}^i(M, N) = 0` for $`i > d`.

Hint: To prove the "if" part, use induction in $`d` and the long exact sequence of Ext groups in Problem 8.2.6(v).

(ii) Let $`0 \to M \to P \to N \to 0` be a nonsplit short exact sequence, and assume that $`P` is projective. Show that $`\operatorname{pd}(N) = \operatorname{pd}(M) + 1`.

(iii) Show that if $`\operatorname{pd}(M) = d > 0` and $`P_\bullet` is any projective resolution of $`M`, then the kernel $`K_d` of the map $`P_{d-1} \to P_{d-2}` in this
resolution is projective (where we agree that $`P_{-1} = M`). Thus, by replacing $`P_d` with $`K_d` and all terms to the left of $`P_d` by zero, we get a projective resolution of $`M` of length $`d`. Deduce that if $`A` and $`M` are finite dimensional, then there is a finite resolution $`P_\bullet` of $`M` with finite dimensional $`P_i`.

## Formalization
%%%
tag := "Chapter9/Problem9.4.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.CategoryTheory.Abelian.ProjectiveDimension.exists_finite_projectiveResolution_of_hasProjectiveDimensionLE}

{Manual.docstring RepresentationTheory.CategoryTheory.Abelian.ProjectiveDimension.hasProjectiveDimensionLE_iff_ext_subsingleton}

{Manual.docstring RepresentationTheory.CategoryTheory.Abelian.ProjectiveDimension.projectiveResolution_object_projective_of_hasProjectiveDimensionLE}

{Manual.docstring RepresentationTheory.CategoryTheory.Abelian.ProjectiveDimension.projectiveResolution_structure_of_hasProjectiveDimensionLE}

{Manual.docstring RepresentationTheory.CategoryTheory.Abelian.ProjectiveDimension.right_endpoint_value_eq_left_endpoint_value_add_one_of_shortExact_of_projective_middle_of_no_splitting}

### Supporting declarations

{Manual.docstring RepresentationTheory.AuxiliaryProjectiveResolution.exists_finite_projectiveResolution}
