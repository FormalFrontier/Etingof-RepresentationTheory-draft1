/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Definition5231

#doc (Manual) "Algebraic (rational, polynomial) representation of GL(V)" =>

# Algebraic (rational, polynomial) representation of GL(V)
%%%
tag := "Chapter5/Definition5.23.1"
number := false
%%%

*Definition 5.23.1.* We say that a finite dimensional representation $`Y` of $`GL(V)` is *algebraic* (or *rational*, or *polynomial*) if its matrix elements are polynomial functions of the entries of $`g`, $`g^{-1}`, $`g \in GL(V)` (i.e., belong to $`k[g_{ij}][1/\det(g)]`).

## Formalization
%%%
tag := "Chapter5/Definition5.23.1/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty}

{Manual.docstring RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryRepresentationProperty}

{Manual.docstring RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryRepresentationProperty_iff_mapProperty}

{Manual.docstring RepresentationTheory.GeneralLinearGroup.Auxiliary.exists_auxiliaryMap_ne_id_at_one}
