/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter6.Definition641

#doc (Manual) "Definition 6.4.1: Cartan matrix" =>

# Definition 6.4.1: Cartan matrix
%%%
tag := "Chapter6/Definition6.4.1"
number := false
%%%

*Definition 6.4.1* (Cartan matrix). We define the *Cartan matrix* of $`\Gamma` as

$$`A = 2\operatorname{Id} - R.`

On the lattice $`\mathbb{Z}^n` (or the space $`\mathbb{R}^n`) we then define an inner product

$$`B(x, y) = x^T A y`

corresponding to the graph $`\Gamma`.

## Formalization
%%%
tag := "Chapter6/Definition6.4.1/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.AuxiliaryIntegerMatrixTransform.auxiliaryTransform}
