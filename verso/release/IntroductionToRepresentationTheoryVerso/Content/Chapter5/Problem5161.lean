/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Problem5161

#doc (Manual) "Branching rules: restriction and induction for S\\_n representations" =>

# Branching rules: restriction and induction for S\_n representations
%%%
tag := "Chapter5/Problem5.16.1"
number := false
%%%

*Problem 5.16.1.* For a Young diagram $`\mu`, let $`A(\mu)` be the set of Young diagrams obtained by adding a square to $`\mu`, and let $`R(\mu)` be the set of Young diagrams obtained by removing a square from $`\mu`.

(a) Show that $`\operatorname{Res}_{S_{n-1}}^{S_n} V_\mu = \bigoplus_{\lambda \in R(\mu)} V_\lambda`.

(b) Show that $`\operatorname{Ind}_{S_{n-1}}^{S_n} V_\mu = \bigoplus_{\lambda \in A(\mu)} V_\lambda`.

## Formalization
%%%
tag := "Chapter5/Problem5.16.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Auxiliary.FDRepPartitions.auxiliaryFDRepOfPartitionIso}

{Manual.docstring RepresentationTheory.Auxiliary.FDRepPartitions.auxiliaryFDRepOfSuccessorPartitionIso}
