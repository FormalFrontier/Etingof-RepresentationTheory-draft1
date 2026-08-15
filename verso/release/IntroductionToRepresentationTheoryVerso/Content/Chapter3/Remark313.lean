/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.Remark313

#doc (Manual) "Canonical decomposition of semisimple representations via Schur's lemma" =>
# Canonical decomposition of semisimple representations via Schur's lemma
%%%
tag := "Chapter3/Remark3.1.3"
number := false
%%%
**Remark 3.1.3.** Note that by Schur's lemma, any semisimple finite dimensional representation $`V` of $`A` is canonically identified with $`\bigoplus_X \operatorname{Hom}_A(X, V) \otimes X`, where $`X` runs over all irreducible representations of $`A`. Indeed, we have a natural map $`f : \bigoplus_X \operatorname{Hom}(X, V) \otimes X \to V`, given by $`g \otimes x \to g(x)`, $`x \in X`, $`g \in \operatorname{Hom}(X, V)`, and it is easy to verify that this map is an isomorphism. Indeed, if the result holds for representations $`V_i` for $`i \in I`, then it holds for their direct sum. Therefore one may assume that $`V` is irreducible.

## Formalization
%%%
tag := "Chapter3/Remark3.1.3/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Module.IsotypicDecomposition.endomorphismTensorSelfEquiv}

{Manual.docstring RepresentationTheory.Module.IsotypicDecomposition.isotypicEvaluation}

{Manual.docstring RepresentationTheory.Module.IsotypicDecomposition.isotypicEvaluation_lof_tmul}

### Supporting declarations

{Manual.docstring RepresentationTheory.Module.IsotypicDecomposition.endomorphismTensorSelfEquiv_tmul}

{Manual.docstring RepresentationTheory.Module.IsotypicDecomposition.homTensorEvaluation}

{Manual.docstring RepresentationTheory.Module.IsotypicDecomposition.homTensorEvaluation_tmul}

{Manual.docstring RepresentationTheory.Module.IsotypicDecomposition.isotypicDecompositionEquiv}

{Manual.docstring RepresentationTheory.Module.IsotypicDecomposition.isotypicEvaluation_injective}

{Manual.docstring RepresentationTheory.Module.IsotypicDecomposition.isotypicEvaluation_surjective}
