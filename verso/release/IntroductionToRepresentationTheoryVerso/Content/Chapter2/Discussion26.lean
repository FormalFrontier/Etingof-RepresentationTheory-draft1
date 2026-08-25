/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Discussion26

#doc (Manual) "Section 2.6: Algebras defined by generators and relations" =>
# Section 2.6: Algebras defined by generators and relations
%%%
tag := "Chapter2/Discussion_2.6"
number := false
%%%

## 2.6. Algebras defined by generators and relations
%%%
tag := "Chapter2/Discussion_2.6/heading-1"
%%%

If $`f_1, \ldots, f_m` are elements of the free algebra $`k\langle x_1, \ldots, x_n \rangle`, we say that the algebra $`A := k\langle x_1, \ldots, x_n \rangle / \langle \{f_1, \ldots, f_m\} \rangle` is **generated** by $`x_1, \ldots, x_n` with **defining relations** $`f_1 = 0, \ldots, f_m = 0`.

## Formalization
%%%
tag := "Chapter2/Discussion_2.6/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.FreeAlgebra.RelationQuotient.FreeAlgebra.AuxiliaryType.algebra_adjoin_generators_eq_top}

{Manual.docstring RepresentationTheory.FreeAlgebra.RelationQuotient.FreeAlgebra.AuxiliaryType.auxiliaryAlgHom_relation}

{Manual.docstring RepresentationTheory.FreeAlgebra.RelationQuotient.FreeAlgebra.AuxiliaryType.eq_ringConQuotient_span_range}

### Supporting declarations

{Manual.docstring RepresentationTheory.FreeAlgebra.RelationQuotient.FreeAlgebra.AuxiliaryType}

{Manual.docstring RepresentationTheory.FreeAlgebra.RelationQuotient.FreeAlgebra.AuxiliaryType.of}
