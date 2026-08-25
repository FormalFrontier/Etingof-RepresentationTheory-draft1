/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso Genre

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Remark232

#doc (Manual) "Left and right modules over commutative rings" =>
# Left and right modules over commutative rings
%%%
tag := "Chapter2/Remark2.3.2"
number := false
%%%
*Remark 2.3.2.* Let $`M` be a left module over a commutative ring $`A`. Then one can regard $`M` as a right $`A`-module, with $`ma := am`. Similarly, any right $`A`-module can be regarded as a left $`A`-module. For this reason, for commutative rings one does not distinguish between left and right $`A`-modules and just calls them $`A`-modules.

## Formalization
%%%
tag := "Chapter2/Remark2.3.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Module.CommutativeOppositeScalars.smul_eq_op_smul}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.Module.CommutativeOppositeScalars.moduleOfMulOpposite}

{Manual.docstring RepresentationTheory.Algebra.Module.CommutativeOppositeScalars.moduleOverMulOpposite}

{Manual.docstring RepresentationTheory.Algebra.Module.CommutativeOppositeScalars.op_smul_eq_smul}
