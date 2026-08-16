/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Problem512

#doc (Manual) "Endomorphism algebras and real type characterization" =>

# Endomorphism algebras and real type characterization
%%%
tag := "Chapter5/Problem5.1.2"
number := false
%%%

**Problem 5.1.2.** (a) Show that $`\operatorname{End}_{\mathbb{R}[G]} V` is $`\mathbb{C}` for $`V` of complex type, $`\operatorname{Mat}_2(\mathbb{R})` for $`V` of real type, and $`\mathbb{H}` for $`V` of quaternionic type, which motivates the names above.

Hint: Show that the complexification $`V_{\mathbb{C}}` of $`V` decomposes as $`V \oplus V^*`. Use this to compute the dimension of $`\operatorname{End}_{\mathbb{R}[G]} V` in all three cases. Using the fact that $`\mathbb{C} \subset \operatorname{End}_{\mathbb{R}[G]} V`, prove the result in the
complex case. In the remaining two cases, let $`B` be the invariant bilinear form on $`V` and let $`( \ , \ )` be the invariant positive Hermitian form (they are defined up to a nonzero complex scalar and a positive real scalar, respectively). Define the operator $`j : V \to V` such that $`B(v, w) = (v, jw)`. Show that $`j` is complex antilinear ($`ji = -ij`), and $`j^2 = \lambda \cdot \operatorname{Id}`, where $`\lambda` is a real number, positive in the real case and negative in the quaternionic case (if $`B` is renormalized, $`j` multiplies by a nonzero complex number $`z` and $`j^2` by $`z\bar{z}`, as $`j` is antilinear). Thus $`j` can be normalized so that $`j^2 = 1` in the real case and $`j^2 = -1` in the quaternionic case. Deduce the claim from this.

(b) Show that $`V` is of real type if and only if $`V` is the complexification of a representation $`V_{\mathbb{R}}` over the field of real numbers.

## Formalization
%%%
tag := "Chapter5/Problem5.1.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Complex.RealEndomorphismCentralizer.Representation.auxiliaryCondition_iff_exists_invariantRealSubmodule}

{Manual.docstring RepresentationTheory.Complex.RealEndomorphismCentralizer.Representation.nonempty_realEndomorphismCentralizer_algEquiv_complex}

{Manual.docstring RepresentationTheory.Complex.RealEndomorphismCentralizer.Representation.nonempty_realEndomorphismCentralizer_algEquiv_matrixFinTwo}

{Manual.docstring RepresentationTheory.Complex.RealEndomorphismCentralizer.Representation.nonempty_realEndomorphismCentralizer_algEquiv_quaternion}

### Supporting declarations

{Manual.docstring RepresentationTheory.Complex.RealEndomorphismCentralizer.Representation.auxiliaryCondition_of_exists_invariantRealSubmodule}

{Manual.docstring RepresentationTheory.Complex.RealEndomorphismCentralizer.Representation.exists_invariantRealSubmodule_of_auxiliaryCondition}

{Manual.docstring RepresentationTheory.Complex.RealEndomorphismCentralizer.Representation.realEndomorphismCentralizer}
