/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.DiscussionPureTensors

#doc (Manual) "Pure tensors and tensor products of multiple spaces" =>
# Pure tensors and tensor products of multiple spaces
%%%
tag := "Chapter2/Discussion_pure_tensors"
number := false
%%%
The elements $`v \otimes w \in V \otimes W`, for $`v \in V, w \in W` are called pure tensors. Note that in general, there are elements of $`V \otimes W` which are not pure tensors.
This allows one to define the tensor product of any number of vector spaces, $`V_1 \otimes \cdots \otimes V_n`. Note that this tensor product is associative, in the sense that $`(V_1 \otimes V_2) \otimes V_3` can be naturally identified with $`V_1 \otimes (V_2 \otimes V_3)`.

In particular, people often consider tensor products of the form $`V^{\otimes n} = V \otimes \cdots \otimes V` ($`n` times) for a given vector space $`V`, and, more generally, $`E := V^{\otimes n} \otimes (V^*)^{\otimes m}`. This space is called **the space of tensors of type** $`(m, n)` on $`V`. For instance, tensors of type $`(0, 1)` are vectors, tensors of type $`(1, 0)` — linear functionals (covectors), tensors of type $`(1, 1)` — linear operators, of type $`(2, 0)` — bilinear forms, tensors of type $`(2, 1)` — algebra structures, etc.

## Formalization
%%%
tag := "Chapter2/Discussion_pure_tensors/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.LinearAlgebra.TensorProductAuxiliary.tensorAux_ne_tmul}

### Supporting declarations

{Manual.docstring RepresentationTheory.LinearAlgebra.TensorOperations.AuxiliaryType_aux2}

{Manual.docstring RepresentationTheory.LinearAlgebra.TensorProductAuxiliary.moduleAuxiliaryType}
