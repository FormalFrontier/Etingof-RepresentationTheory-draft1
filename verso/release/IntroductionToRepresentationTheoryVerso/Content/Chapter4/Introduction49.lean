/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter4.Introduction49

#doc (Manual) "Section 4.9: Computing tensor product multiplicities using character tables" =>

# Section 4.9: Computing tensor product multiplicities using character tables
%%%
tag := "Chapter4/Introduction_4.9"
number := false
%%%

## 4.9. Computing tensor product multiplicities using character tables
%%%
tag := "Chapter4/Introduction_4.9/heading-1"
%%%

Character tables allow us to compute the tensor product multiplicities $`N^k_{ij}` using

$$`V_i \otimes V_j = \sum N^k_{ij} V_k, \quad N^k_{ij} = (\chi_i \chi_j, \chi_k).`

## Formalization
%%%
tag := "Chapter4/Introduction_4.9/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.FiniteGroupTensorProductDecomposition.cast_tensorProductMultiplicity_eq_character_average}

### Supporting declarations

{Manual.docstring RepresentationTheory.FiniteGroupTensorProductDecomposition.tensorProductMultiplicity}

{Manual.docstring RepresentationTheory.FiniteGroupTensorProductDecomposition.tensorProduct_exists_simpleDecomposition}

{Manual.docstring RepresentationTheory.FiniteGroupTensorProductDecomposition.tensorProduct_iso_auxiliaryDecomposition}
