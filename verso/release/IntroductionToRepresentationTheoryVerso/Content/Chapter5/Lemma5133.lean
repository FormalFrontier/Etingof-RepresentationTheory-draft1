/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Lemma5133

#doc (Manual) "c\\_lambda is proportional to an idempotent" =>

# c\_lambda is proportional to an idempotent
%%%
tag := "Chapter5/Lemma5.13.3"
number := false
%%%

*Lemma 5.13.3.* $`c_\lambda` _is proportional to an idempotent. Namely,_ $`c_\lambda^2 = \frac{n!}{|P_\lambda||Q_\lambda| \dim V_\lambda} c_\lambda`.

*Proof.* Lemma 5.13.1 implies that $`c_\lambda^2` is proportional to $`c_\lambda`. Also, it is easy to see that the trace of $`c_\lambda` in the regular representation is $`n! |P_\lambda|^{-1} |Q_\lambda|^{-1}` (as the coefficient of the identity element in $`c_\lambda` is $`|P_\lambda|^{-1} |Q_\lambda|^{-1}`). This implies the statement. $`\square`

## Formalization
%%%
tag := "Chapter5/Lemma5.13.3/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Nat.Partition.ScalarMultiplication.partitionIndexedElement_mul_self_eq_smul_self}
