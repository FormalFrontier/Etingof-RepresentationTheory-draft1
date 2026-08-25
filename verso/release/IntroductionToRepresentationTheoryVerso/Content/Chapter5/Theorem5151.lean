/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Theorem5151

#doc (Manual) "Frobenius character formula for Specht modules V\\_lambda" =>

# Frobenius character formula for Specht modules V\_lambda
%%%
tag := "Chapter5/Theorem5.15.1"
number := false
%%%

*Theorem 5.15.1.* _Let $`N \geq p`. Then $`\chi_{V_\lambda}(C_\mathbf{i})` is the coefficient of $`x^{\lambda+\rho} := \prod x_j^{\lambda_j + N - j}` in the polynomial_

$$`\Delta(x) \prod_{m \geq 1} H_m(x)^{i_m}.`

## Formalization
%%%
tag := "Chapter5/Theorem5.15.1/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.PartitionPolynomials.signedAuxiliaryValue_eq_coefficient}

{Manual.docstring RepresentationTheory.SymmetricGroup.PartitionCharacterPolynomial.SymmetricGroup.PartitionCharacter.auxiliarySignSmul_eq_coefficient}
