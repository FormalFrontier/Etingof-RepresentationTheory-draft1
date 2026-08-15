/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Theorem5181

#doc (Manual) "Double Centralizer Theorem" =>

# Double Centralizer Theorem
%%%
tag := "Chapter5/Theorem5.18.1"
number := false
%%%
**Theorem 5.18.1.** _Let $`A`, $`B` be two subalgebras of the algebra $`\operatorname{End} E` of endomorphisms of a finite dimensional vector space $`E`, such that $`A` is semisimple and $`B = \operatorname{End}_A E`. Then:_

_(i) $`A = \operatorname{End}_B E` (i.e., the centralizer of the centralizer of $`A` is $`A`)._

_(ii) $`B` is semisimple._

_(iii) As a representation of $`A \otimes B`, $`E` decomposes as_

$$`E = \bigoplus_{i \in I} V_i \otimes W_i,`

_where $`V_i` are all the irreducible representations of $`A` and $`W_i` are all the irreducible representations of $`B`. In particular, we have a natural bijection between irreducible representations of $`A` and $`B`._

**Proof.** Since $`A` is semisimple, we have a natural decomposition $`E = \bigoplus_{i \in I} V_i \otimes W_i`, where $`W_i := \operatorname{Hom}_A(V_i, E)` and $`A = \bigoplus_i \operatorname{End} V_i`. Note that $`W_i \neq 0`, since the action of $`A` on $`E` is faithful. Therefore, by
Schur's lemma, $`B = \operatorname{End}_A(E)` is naturally identified with $`\bigoplus_i \operatorname{End}(W_i)`. This implies all the statements of the theorem. $`\square`

## Formalization
%%%
tag := "Chapter5/Theorem5.18.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.CentralizerDecomposition.centralizer_centralizer_eq}

{Manual.docstring RepresentationTheory.CentralizerDecomposition.isSemisimpleRing_centralizer}

### Supporting declarations

{Manual.docstring RepresentationTheory.CentralizerDecomposition.AuxiliaryDecompositionData.ofEquiv}

{Manual.docstring RepresentationTheory.CentralizerDecomposition.exists_auxiliary_decomposition_data}

{Manual.docstring RepresentationTheory.CentralizerDecomposition.exists_auxiliary_evaluation_equiv}

{Manual.docstring RepresentationTheory.IsotypicCentralizer.existsIsSimpleModuleSubmoduleLinearMapEquiv}

{Manual.docstring RepresentationTheory.IsotypicCentralizer.isotypicComponentsEquivCentralizer}

{Manual.docstring RepresentationTheory.IsotypicCentralizer.linearEquivLinearMapPrecomp}

{Manual.docstring RepresentationTheory.IsotypicCentralizer.linearEquivOfCentralizerLinearEquivLinearMap}
