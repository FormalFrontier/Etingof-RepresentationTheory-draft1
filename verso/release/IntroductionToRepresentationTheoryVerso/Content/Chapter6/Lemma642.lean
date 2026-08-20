/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter6.Lemma642

#doc (Manual) "Lemma 6.4.2: B is positive definite and even-valued" =>

# Lemma 6.4.2: B is positive definite and even-valued
%%%
tag := "Chapter6/Lemma6.4.2"
number := false
%%%

*Lemma 6.4.2.* (1) _$`B` is positive definite._

(2) _$`B(x, x)` takes only even values for $`x \in \mathbb{Z}^n`._

*Proof.* (1) This follows by definition, since $`\Gamma` is a Dynkin diagram.

(2) By the definition of the Cartan matrix we get

$$`B(x, x) = x^T A x = \sum_{i,j} x_i a_{ij} x_j = 2 \sum_i x_i^2 + \sum_{i,j,\ i \neq j} x_i a_{ij} x_j`

$$`= 2 \sum_i x_i^2 + 2 \cdot \sum_{i < j} a_{ij} x_i x_j,`

which is even. $`\square`

## Formalization
%%%
tag := "Chapter6/Lemma6.4.2/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.LinearAlgebra.Matrix.TwoIdentitySub.Matrix.dotProduct_mulVec_two_smul_one_sub_pos}

{Manual.docstring RepresentationTheory.LinearAlgebra.Matrix.TwoIdentitySub.Matrix.even_dotProduct_mulVec_two_smul_one_sub}
