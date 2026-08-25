/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.Remark3103

#doc (Manual) "Failure of Theorem 3.10.2 for infinite dimensional representations" =>

# Failure of Theorem 3.10.2 for infinite dimensional representations
%%%
tag := "Chapter3/Remark3.10.3"
number := false
%%%
**Remark 3.10.3.** Part (ii) of the theorem typically fails for infinite dimensional representations; e.g. it fails when $`A` is the Weyl algebra in characteristic zero. Part (i) may also fail. E.g. let $`A = B = V = W = \mathbb{C}(x)`. Then (i) fails, as $`A \otimes B` is not a field.

## Formalization
%%%
tag := "Chapter3/Remark3.10.3/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.Module.AuxiliaryRepresentations.auxiliaryTensorProductModule_isSimpleModule}

{Manual.docstring RepresentationTheory.Algebra.Module.AuxiliaryRepresentations.not_equivariant_tensorProductEquiv}

{Manual.docstring RepresentationTheory.Algebra.Module.AuxiliaryRepresentations.not_isField_tensorProduct_ratFunc_self}
