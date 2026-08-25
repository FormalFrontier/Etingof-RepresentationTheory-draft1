/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Proposition5251

#doc (Manual) "\\[G,G\\] = SL\\_2(F\\_q)" =>

# \[G,G\] = SL\_2(F\_q)
%%%
tag := "Chapter5/Proposition5.25.1"
number := false
%%%
**Proposition 5.25.1.** $`[G, G] = SL_2(\mathbb{F}_q)`.

**Proof.** Clearly,

$$`\det(xyx^{-1}y^{-1}) = 1,`

so

$$`[G, G] \subseteq SL_2(\mathbb{F}_q).`

To show the converse, it suffices to show that the matrices

$$`\begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}, \qquad \begin{pmatrix} a & 0 \\ 0 & a^{-1} \end{pmatrix}, \qquad \begin{pmatrix} 1 & 0 \\ 1 & 1 \end{pmatrix}`

are commutators (as such matrices generate $`SL_2(\mathbb{F}_q)`). Clearly, by using transposition, it suffices to show that only the first two matrices are commutators. But it is easy to see that the matrix

$$`\begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}`
is the commutator of the matrices

$$`A = \begin{pmatrix} 1 & 1/2 \\ 0 & 1 \end{pmatrix}, \qquad B = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix},`

while the matrix

$$`\begin{pmatrix} a & 0 \\ 0 & a^{-1} \end{pmatrix}`

is the commutator of the matrices

$$`A = \begin{pmatrix} a & 0 \\ 0 & 1 \end{pmatrix}, \qquad B = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}.`

This completes the proof. $`\square`

## Formalization
%%%
tag := "Chapter5/Proposition5.25.1/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.SpecialLinear.Commutator.generalLinear_commutator_eq_specialLinear_range}
