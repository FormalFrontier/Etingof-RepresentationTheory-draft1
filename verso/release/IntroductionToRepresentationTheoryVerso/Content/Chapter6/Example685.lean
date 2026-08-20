/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter6.Example685

#doc (Manual) "Example 6.8.5: Reflection functors on D4" =>

# Example 6.8.5: Reflection functors on D4
%%%
tag := "Chapter6/Example6.8.5"
number := false
%%%

*Example 6.8.5.* Let us demonstrate by example how reflection functors work. Consider the quiver $`D_4` with the orientation of all arrows towards the node (which is labeled by 4). Start with the 1-dimensional representation $`V_{\alpha_4}` sitting at the fourth vertex. Apply to $`V_{\alpha_4}` the functor $`F_3^- F_2^- F_1^-`. This yields

$$`F_1^- F_2^- F_3^- V_{\alpha_4} = V_{\alpha_1 + \alpha_2 + \alpha_3 + \alpha_4}.`

Now applying $`F_4^-`, we get

$$`F_4^- F_1^- F_2^- F_3^- V_{\alpha_4} = V_{\alpha_1 + \alpha_2 + \alpha_3 + 2\alpha_4}.`

Note that this is exactly the inclusion of three lines into the plane, which is the most complicated indecomposable representation of the $`D_4` quiver.

## Formalization
%%%
tag := "Chapter6/Example6.8.5/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.IntegerMatrices.integerMatrixB_operationAtThreeZeroOneTwo_eq_oneOneOneTwo}

{Manual.docstring RepresentationTheory.IntegerMatrices.integerMatrixB_operationAtZeroOneTwo_eq_ones}

{Manual.docstring RepresentationTheory.IntegerMatrices.tuple2111_mem}
