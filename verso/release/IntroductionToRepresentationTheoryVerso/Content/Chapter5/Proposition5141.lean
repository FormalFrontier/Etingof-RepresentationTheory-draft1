/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Proposition5141

#doc (Manual) "Decomposition of U\\_lambda in terms of V\\_mu with Kostka numbers" =>

# Decomposition of U\_lambda in terms of V\_mu with Kostka numbers
%%%
tag := "Chapter5/Proposition5.14.1"
number := false
%%%

*Proposition 5.14.1.* _We have $`\operatorname{Hom}(U_\lambda, V_\mu) = 0` for $`\mu < \lambda` and $`\dim \operatorname{Hom}(U_\lambda, V_\lambda) = 1`. Thus, $`U_\lambda = \bigoplus_{\mu \geq \lambda} K_{\mu\lambda} V_\mu`, where $`K_{\mu\lambda}` are nonnegative integers and $`K_{\lambda\lambda} = 1`._

## Formalization
%%%
tag := "Chapter5/Proposition5.14.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.AuxiliaryPartitionLinearIndependentFamily.auxiliary_nat_values_eq}

### Supporting declarations

{Manual.docstring RepresentationTheory.AuxiliaryPartitionLinearEquivalences.auxiliaryDirectSumLinearEquiv}

{Manual.docstring RepresentationTheory.PartitionLinearMapVanishing.finrank_linearMap_to_mem_eq_one}

{Manual.docstring RepresentationTheory.PartitionLinearMapVanishing.linearMap_to_mem_eq_zero_of_lexLt}

{Manual.docstring RepresentationTheory.PartitionLinearMapVanishing.linearMap_to_mem_eq_zero_of_not_partitionRelation}
