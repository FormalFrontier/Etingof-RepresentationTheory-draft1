/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Problem2318

#doc (Manual) "Infinite dimensional Schur lemma (Dixmier)" =>
# Infinite dimensional Schur lemma (Dixmier)
%%%
tag := "Chapter2/Problem2.3.18"
number := false
%%%
**Problem 2.3.18.** Prove the following "infinite dimensional Schur lemma" (due to Dixmier): Let $`A` be an algebra over $`\mathbb{C}` and let $`V` be an irreducible representation of $`A` with at most countable basis. Then any homomorphism of representations $`\phi : V \to V` is a scalar operator.

Hint: By the usual Schur's lemma, the algebra $`D := \operatorname{End}_A(V)` is an algebra with division. Show that $`D` is at most countably dimensional. Suppose $`\phi` is not a scalar, and consider the subfield $`\mathbb{C}(\phi) \subset D`.
Show that $`\mathbb{C}(\phi)` is a transcendental extension of $`\mathbb{C}`. Derive from this that $`\mathbb{C}(\phi)` is uncountably dimensional and obtain a contradiction.

## Formalization
%%%
tag := "Chapter2/Problem2.3.18/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.SimpleModule.ScalarEndomorphisms.linearMap_eq_smul_of_simple_of_rank_le_aleph0}
