/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Example2314

#doc (Manual) "Irreducible and indecomposable representations of k and k\\[x\\]" =>
# Irreducible and indecomposable representations of k and k\[x\]
%%%
tag := "Chapter2/Example2.3.14"
number := false
%%%
**Example 2.3.14.** 1. $`A = k`. Since representations of $`A` are simply vector spaces, $`V = A` is the only irreducible and the only indecomposable representation.

2. $`A = k[x]`. Since this algebra is commutative, the irreducible finite dimensional representations of $`A` are its 1-dimensional representations. As we discussed above, they are defined by a single operator $`\rho(x)`. In the 1-dimensional case, this is just a number from $`k`. So all the irreducible finite dimensional representations of $`A` are $`V_\lambda = k`, $`\lambda \in k`, in which the action of $`A` is defined by $`\rho(x) = \lambda`. Clearly, these representations are pairwise nonisomorphic.

The classification of finite dimensional indecomposable representations of $`k[x]` is more interesting. To obtain it, recall that any linear operator on a finite dimensional vector space $`V` can be brought to Jordan normal form. More specifically, recall that the Jordan block $`J_{\lambda,n}` is the operator on $`k^n` which in the standard basis is given by the formulas $`J_{\lambda,n} e_i = \lambda e_i + e_{i-1}` for $`i > 1` and $`J_{\lambda,n} e_1 = \lambda e_1`. Then for any linear operator $`B : V \to V` there exists a basis of $`V` such that the matrix of $`B` in this basis is a direct sum of Jordan blocks. This implies that all the indecomposable finite dimensional representations of $`A` are $`V_{\lambda,n} = k^n`, $`\lambda \in k`, with $`\rho(x) = J_{\lambda,n}`. The fact that these representations are indecomposable and pairwise nonisomorphic follows from the Jordan normal form theorem (which in particular says that the Jordan normal form of an operator is unique up to permutation of blocks).

This example shows that an indecomposable representation of an algebra need not be irreducible.

## Formalization
%%%
tag := "Chapter2/Example2.3.14/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.equiv_field_of_isSimpleModule}

{Manual.docstring RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.exists_equiv_pi_jordanBlock}

{Manual.docstring RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.finrank_quotient_maximalIdeal}

{Manual.docstring RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.isIndecomposableModule_and_not_isSimpleModule_jordanBlock_two}

{Manual.docstring RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.jordanBlockModule_equiv_iff}

### Supporting declarations

{Manual.docstring RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.JordanBlockModule}

{Manual.docstring RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.auxiliaryFact}

{Manual.docstring RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.equiv_field_of_isIndecomposableModule}

{Manual.docstring RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.equiv_jordanBlock_of_isIndecomposableModule}

{Manual.docstring RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.jordanBlockModule_isIndecomposable}

{Manual.docstring RepresentationTheory.RingTheory.Polynomial.JordanBlockModule.jordanOperator}
