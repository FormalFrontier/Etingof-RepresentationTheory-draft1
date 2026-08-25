/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Exercise2115

#doc (Manual) "Base change for algebras and modules" =>
# Base change for algebras and modules
%%%
tag := "Chapter2/Exercise2.11.5"
number := false
%%%
**Exercise 2.11.5.** Let $`K` be a field, and let $`L` be an extension of $`K`. If $`A` is an algebra over $`K`, show that $`A \otimes_K L` is naturally an algebra over $`L`. Show that if $`V` is an $`A`-module, then $`V \otimes_K L` has a natural structure of a module over the algebra $`A \otimes_K L`.

## Formalization
%%%
tag := "Chapter2/Exercise2.11.5/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.TensorProduct.ScalarExtension.rightTensorProductAlgebra}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.TensorProduct.ScalarExtension.algebraMap_apply}

{Manual.docstring RepresentationTheory.Algebra.TensorProduct.ScalarExtension.exists_tensorProductModule}
