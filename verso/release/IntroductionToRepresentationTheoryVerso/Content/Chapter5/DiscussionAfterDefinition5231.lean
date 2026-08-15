/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.DiscussionAfterDefinition5231

#doc (Manual) "Algebraic representations and highest weight" =>

# Algebraic representations and highest weight
%%%
tag := "Chapter5/Discussion_after_Definition5.23.1"
number := false
%%%

Note that subrepresentations, quotients, direct sums, tensor products and duals of algebraic representations are algebraic. For example, $`V^{\otimes n}` and hence all $`L_\lambda` are algebraic. Also define $`L_{\lambda - r \cdot 1^N} := L_\lambda \otimes (\wedge^N V^*)^{\otimes r}` (this definition makes sense by Proposition 5.22.2). This is also an algebraic representation. Thus we have attached a unique irreducible algebraic representation $`L_\lambda` of $`GL(V) = GL_N` to any sequence $`(\lambda_1, \ldots, \lambda_N)` of integers (not necessarily positive) such that $`\lambda_1 \geq \cdots \geq \lambda_N`. This sequence is called the *highest weight* of $`L_\lambda`.

## Formalization
%%%
tag := "Chapter5/Discussion_after_Definition5.23.1/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.AuxiliaryModuleData.auxiliaryIndex}

{Manual.docstring RepresentationTheory.Representation.ModuleEquivAndTraceSeparation.isSimpleModule_fdRep_of_antitone}
