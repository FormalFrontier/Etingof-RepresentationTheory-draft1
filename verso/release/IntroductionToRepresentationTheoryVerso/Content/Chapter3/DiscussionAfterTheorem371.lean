/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.DiscussionAfterTheorem371

#doc (Manual) "Length of a representation and Jordan-Holder series" =>

# Length of a representation and Jordan-Holder series
%%%
tag := "Chapter3/Discussion_after_Theorem3.7.1"
number := false
%%%
The Jordan-Holder theorem shows that the number $`n` of terms in a filtration of $`V` with irreducible successive quotients does not depend on the choice of a filtration and depends only on $`V`. This number is called the **length** of $`V`. It is easy to see that $`n` is also the maximal length of a filtration of $`V` in which all the inclusions are strict.

The sequence of the irreducible representations $`W_1, \ldots, W_n` enumerated in the order they appear from some filtration of $`V` as successive quotients is called a **Jordan-Holder series** of $`V`.

## Formalization
%%%
tag := "Chapter3/Discussion_after_Theorem3.7.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Module.CompositionSeriesEquivalence.length_eq}

### Supporting declarations

{Manual.docstring RepresentationTheory.Module.CompositionSeriesLength.compositionSeries_length_isGreatest}
