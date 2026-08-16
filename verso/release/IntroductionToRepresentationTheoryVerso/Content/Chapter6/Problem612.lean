/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter6.Problem612

#doc (Manual) "Problem 6.1.2: Some algebraic geometry" =>

# Problem 6.1.2: Some algebraic geometry
%%%
tag := "Chapter6/Problem6.1.2"
number := false
%%%

*Problem 6.1.2.* Some algebraic geometry. Let $`k` be an algebraically closed field, and let $`G = GL_m(k)`. Let $`V` be an algebraic representation of $`G`. Show that if $`G` has finitely many orbits on $`V`, then $`\dim(V) \leq m^2`. Namely:

(a) Let $`x_1, \ldots, x_N` be linear coordinates on $`V`. Let us say that a subset $`X` of $`V` is *Zariski dense* if any polynomial $`f(x_1, \ldots, x_N)` which vanishes on $`X` is zero (coefficientwise). Show that if $`G` has finitely many orbits on $`V`, then $`G` has at least one Zariski dense orbit on $`V`.

(b) Use (a) to construct a field embedding $`k(x_1, \ldots, x_N) \to k(g_{pq})`. Then use Problem 6.1.1.

(c) Generalize the result of this problem to the case when $`G = GL_{m_1}(k) \times \cdots \times GL_{m_n}(k)`.

## Formalization
%%%
tag := "Chapter6/Problem6.1.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.PolynomialRepresentation.FiniteOrbits.exists_isPolynomiallyDense_orbit_of_finite_orbits}

{Manual.docstring RepresentationTheory.PolynomialRepresentation.FiniteOrbits.finrank_le_sq_of_finite_representation_orbits}

{Manual.docstring RepresentationTheory.PolynomialRepresentation.FiniteOrbits.finrank_le_sum_sq_of_finite_representation_orbits}

### Supporting declarations

{Manual.docstring RepresentationTheory.PolynomialRepresentation.FiniteOrbits.exists_injective_localizedMatrixVectorSubstitutionAlgHom_of_finite_orbits}
