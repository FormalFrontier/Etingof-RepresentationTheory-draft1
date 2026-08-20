/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter6.Proposition665

#doc (Manual) "Proposition 6.6.5: Indecomposable reps are surjective at sinks / injective at sources" =>

# Proposition 6.6.5: Indecomposable reps are surjective at sinks / injective at sources
%%%
tag := "Chapter6/Proposition6.6.5"
number := false
%%%

*Proposition 6.6.5.* _Let $`Q` be a quiver and $`V` be an indecomposable representation of $`Q`._

_(1) Let $`i \in Q` be a sink. Then either $`\dim V_i = 1`, $`\dim V_j = 0` for $`j \neq i` or_

$$`
\varphi : \bigoplus_{j \to i} V_j \to V_i
`

_is surjective._

_(2) Let $`i \in Q` be a source. Then either $`\dim V_i = 1`, $`\dim V_j = 0` for $`j \neq i` or_

$$`
\psi : V_i \to \bigoplus_{i \to j} V_j
`

_is injective._

*Proof.* (1) Choose a complement $`W` of $`\operatorname{Im} \varphi`. Then we get

$$`
V = \begin{array}{c} & W \\ 0 \to \bullet \leftarrow 0 \\ & \uparrow \\ & 0 \end{array} \oplus V'.
`
Since $`V` is indecomposable, one of these summands has to be zero. If the first summand is zero, then $`\varphi` has to be surjective. If the second summand is zero, then the first one has to be of the desired form, because else we could write it as a direct sum of several objects of the type

$$`
\overset{0}{\bullet} \to \overset{1}{\bullet} \leftarrow \overset{0}{\bullet}
`

$$`
\uparrow
`

$$`
\overset{0}{\bullet}
`

which is impossible since $`V` was supposed to be indecomposable.

(2) This follows similarly by splitting away the kernel of $`\psi`. $`\square`

## Formalization
%%%
tag := "Chapter6/Proposition6.6.5/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.QuiverRepresentation.Auxiliary.QuiverRepresentation.Auxiliary.vertexConditionOrInjective}

{Manual.docstring RepresentationTheory.QuiverRepresentation.Auxiliary.QuiverRepresentation.Auxiliary.vertexConditionOrSurjective}
