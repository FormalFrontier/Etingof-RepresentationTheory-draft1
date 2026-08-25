/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Remark592

#doc (Manual) "Alternative form of the Frobenius formula" =>

# Alternative form of the Frobenius formula
%%%
tag := "Chapter5/Remark5.9.2"
number := false
%%%

**Remark 5.9.2.** If the characteristic of the ground field $`k` is relatively prime to $`|H|`, then this formula can be written as

$$`\chi(g) = \frac{1}{|H|} \sum_{x \in G : xgx^{-1} \in H} \chi_V(xgx^{-1}).`

## Formalization
%%%
tag := "Chapter5/Remark5.9.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.AuxiliaryQuotientSummation.inv_card_mul_sum_eq_sum_quotient}

### Supporting declarations

{Manual.docstring RepresentationTheory.Auxiliary.UnavailableStatement.Auxiliary.statement015437}

{Manual.docstring RepresentationTheory.AuxiliaryUnavailableStatement.auxiliary_theorem}
