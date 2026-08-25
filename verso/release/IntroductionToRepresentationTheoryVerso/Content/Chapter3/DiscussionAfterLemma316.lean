/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.DiscussionAfterLemma316

#doc (Manual) "Completion of alternative proof of Proposition 3.1.4" =>
# Completion of alternative proof of Proposition 3.1.4
%%%
tag := "Chapter3/Discussion_after_Lemma3.1.6"
number := false
%%%
Now we are ready to prove Proposition 3.1.4. Let $`W` be a submodule of $`V := \bigoplus_X V_X \otimes X`, where $`\dim V < \infty`. We claim that $`W = \bigoplus_X W_X \otimes X` for some vector spaces $`W_X \subseteq V_X`. Indeed, by Lemma 3.1.6 have $`V/W = \bigoplus_X U_X \otimes X` for some vector spaces $`U_X`, so

$$`W = \operatorname{Ker}(V \to V/W) = \bigoplus_X \operatorname{Ker}(V_X \to U_X) \otimes X,`

as desired.

## Formalization
%%%
tag := "Chapter3/Discussion_after_Lemma3.1.6/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Module.SemisimpleHomDecomposition.mem_ker_iff_forall_multiplicityComponent_eq_zero}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.Module.ComplementConstructions.exists_map_agreeing_on_iSup_of_internal}

{Manual.docstring RepresentationTheory.Algebra.Module.IsotypicDecomposition.exists_linearIndependent_coordinates_directSum}

{Manual.docstring RepresentationTheory.Algebra.Module.SimpleMatrixCoordinates.exists_injective_coordinates_directSum}

{Manual.docstring RepresentationTheory.Module.SemisimpleHomDecomposition.homMultiplicityMap_apply_apply}

{Manual.docstring RepresentationTheory.Module.SemisimpleHomDecomposition.restrictScalars_eq_semisimpleDecomposition_comp}
