/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.DiscussionVerificationOfInd

#doc (Manual) "Verification that Ind\\_H^G V is a well-defined representation" =>

# Verification that Ind\_H^G V is a well-defined representation
%%%
tag := "Chapter5/Discussion_verification_of_Ind"
number := false
%%%

Let us check that $`\operatorname{Ind}_H^G V` is well defined as a representation. Indeed, we have

$$`g(f)(hx) = f(hxg) = \rho_V(h) f(xg) = \rho_V(h) g(f)(x),`

and

$$`g(g'(f))(x) = g'(f)(xg) = f(xgg') = (gg')(f)(x)`

for any $`g, g', x \in G` and $`h \in H`.

## Formalization
%%%
tag := "Chapter5/Discussion_verification_of_Ind/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.InductionAndCoinduction.coinduced_apply}

{Manual.docstring RepresentationTheory.InductionAndCoinduction.coinduced_equivariance}

{Manual.docstring RepresentationTheory.InductionAndCoinduction.coinduced_mul}

{Manual.docstring RepresentationTheory.InductionAndCoinduction.coinduced_one}

{Manual.docstring RepresentationTheory.InductionAndCoinduction.mem_coinducedSpace_iff}
