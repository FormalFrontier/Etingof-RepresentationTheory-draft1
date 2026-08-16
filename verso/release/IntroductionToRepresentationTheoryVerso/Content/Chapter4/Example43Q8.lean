/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter4.Example43Q8

#doc (Manual) "Irreducible representations of the quaternion group Q\\_8" =>

# Irreducible representations of the quaternion group Q\_8
%%%
tag := "Chapter4/Example4.3_Q8"
number := false
%%%

(3) The quaternion group $`Q_8 = \{\pm 1, \pm i, \pm j, \pm k\}`, with defining relations

$$`i = jk = -kj, \quad j = ki = -ik, \quad k = ij = -ji, \quad -1 = i^2 = j^2 = k^2.`

The five conjugacy classes are $`\{1\}`, $`\{-1\}`, $`\{\pm i\}`, $`\{\pm j\}`, $`\{\pm k\}`, so there are five different irreducible representations, the sum of the squares of whose dimensions is 8, so their dimensions must be 1, 1, 1, 1, and 2.
The center $`Z(Q_8)` is $`\{\pm 1\}`, and $`Q_8/Z(Q_8) \cong \mathbb{Z}_2 \times \mathbb{Z}_2`. The four 1-dimensional irreducible representations of $`\mathbb{Z}_2 \times \mathbb{Z}_2` can be "pulled back" to $`Q_8`. That is, if $`q : Q_8 \to Q_8/Z(Q_8)` is the quotient map and $`\rho` is any representation of $`Q_8/Z(Q_8)`, then $`\rho \circ q` gives a representation of $`Q_8`.

The 2-dimensional representation is $`V = \mathbb{C}^2`, given by $`\rho(-1) = -\mathrm{Id}` and

$$`(4.3.1) \qquad \rho(i) = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}, \qquad \rho(j) = \begin{pmatrix} \sqrt{-1} & 0 \\ 0 & -\sqrt{-1} \end{pmatrix}, \qquad \rho(k) = \begin{pmatrix} 0 & -\sqrt{-1} \\ -\sqrt{-1} & 0 \end{pmatrix}.`

These are the Pauli matrices, which arise in quantum mechanics.

## Formalization
%%%
tag := "Chapter4/Example4.3_Q8/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.GroupRepresentation.QuaternionGroup.ComplexIrreducibles.card_conjClasses_quaternionGroup}

{Manual.docstring RepresentationTheory.GroupRepresentation.QuaternionGroup.ComplexIrreducibles.mem_center_iff}

{Manual.docstring RepresentationTheory.GroupRepresentation.QuaternionGroup.ComplexIrreducibles.standardMatrixRepresentation_a_one}

{Manual.docstring RepresentationTheory.GroupRepresentation.QuaternionGroup.ComplexIrreducibles.standardMatrixRepresentation_xa_three}

{Manual.docstring RepresentationTheory.GroupRepresentation.QuaternionGroup.ComplexIrreducibles.standardMatrixRepresentation_xa_zero}

{Manual.docstring RepresentationTheory.GroupRepresentation.QuaternionGroup.ComplexIrreducibles.standardRepresentation_simple}

### Supporting declarations

{Manual.docstring RepresentationTheory.GroupRepresentation.QuaternionGroup.ComplexIrreducibles.distinguishedRepresentations_pairwise_nonisomorphic}

{Manual.docstring RepresentationTheory.GroupRepresentation.QuaternionGroup.ComplexIrreducibles.linearCharacter}

{Manual.docstring RepresentationTheory.GroupRepresentation.QuaternionGroup.ComplexIrreducibles.representationOfLinearCharacter}

{Manual.docstring RepresentationTheory.GroupRepresentation.QuaternionGroup.ComplexIrreducibles.simpleRepresentation_iso_standard_or_linear}

{Manual.docstring RepresentationTheory.GroupRepresentation.QuaternionGroup.ComplexIrreducibles.sum_sq_finrank_distinguishedRepresentations}
