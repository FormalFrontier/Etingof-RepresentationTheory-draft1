/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.Definition332

#doc (Manual) "Dual representation" =>
# Dual representation
%%%
tag := "Chapter3/Definition3.3.2"
number := false
%%%
**Definition 3.3.2** (Dual representation). Let $`V` be a representation of any algebra $`A`. Then the **dual representation** $`V^*` is the representation of the opposite algebra $`A^{\mathrm{op}}` (or, equivalently, right $`A`-module) with the action

$$`(f \cdot a)(v) := f(av).`

## Formalization
%%%
tag := "Chapter3/Definition3.3.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Module.DualOppositeAction.dualMulOppositeModule}

{Manual.docstring RepresentationTheory.Module.DualOppositeAction.dualMulOpposite_smul_apply}

### Supporting declarations

{Manual.docstring RepresentationTheory.Module.DualOppositeAction.AuxiliaryModuleType}

{Manual.docstring RepresentationTheory.Module.DualOppositeAction.dualMulOppositeSMul}
