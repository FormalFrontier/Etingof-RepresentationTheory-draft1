/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.Problem333

#doc (Manual) "Alternative proof of Theorem 3.3.1 without earlier results" =>
# Alternative proof of Theorem 3.3.1 without earlier results
%%%
tag := "Chapter3/Problem3.3.3"
number := false
%%%
**Problem 3.3.3.** The goal of this problem is to give an alternative proof of Theorem 3.3.1, not using any of the previous results of Chapter 3.

Let $`A_1`, $`A_2`, $`\ldots`, $`A_n` be $`n` algebras with units $`1_1`, $`1_2`, $`\ldots`, $`1_n`, respectively. Let $`A = A_1 \oplus A_2 \oplus \cdots \oplus A_n`. Clearly, $`1_i 1_j = \delta_{ij} 1_i`, and the unit of $`A` is $`1 = 1_1 + 1_2 + \cdots + 1_n`.

For every representation $`V` of $`A`, it is easy to see that $`1_i V` is a representation of $`A_i` for every $`i \in \{1, 2, \ldots, n\}`. Conversely, if $`V_1`, $`V_2`, $`\ldots`, $`V_n` are representations of $`A_1`, $`A_2`, $`\ldots`, $`A_n`, respectively, then $`V_1 \oplus V_2 \oplus \cdots \oplus V_n` canonically becomes a representation of $`A` (with $`(a_1, a_2, \ldots, a_n) \in A` acting on $`V_1 \oplus V_2 \oplus \cdots \oplus V_n` as $`(v_1, v_2, \ldots, v_n) \mapsto (a_1 v_1, a_2 v_2, \ldots, a_n v_n)`).

(a) Show that a representation $`V` of $`A` is irreducible if and only if $`1_i V` is an irreducible representation of $`A_i` for exactly one $`i \in \{1, 2, \ldots, n\}`, while $`1_i V = 0` for all the other $`i`. Thus, classify the irreducible representations of $`A` in terms of those of $`A_1`, $`A_2`, $`\ldots`, $`A_n`.

(b) Let $`d \in \mathbb{N}`. Show that the only irreducible representation of $`\operatorname{Mat}_d(k)` is $`k^d`, and every finite dimensional representation of $`\operatorname{Mat}_d(k)` is a direct sum of copies of $`k^d`.

Hint: For every $`(i, j) \in \{1, 2, \ldots, d\}^2`, let $`E_{ij} \in \operatorname{Mat}_d(k)` be the matrix with $`1` in the $`i`th row of the $`j`th column and $`0`'s everywhere else. Let $`V` be a finite dimensional representation of $`\operatorname{Mat}_d(k)`. Show that $`V = E_{11}V \oplus E_{22}V \oplus \cdots \oplus E_{dd}V`, and that $`\Phi_i : E_{11}V \to E_{ii}V`, $`v \mapsto E_{i1}v` is an isomorphism for every $`i \in \{1, 2, \ldots, d\}`. For every $`v \in E_{11}V`, denote $`S(v) = \langle E_{11}v, E_{21}v, \ldots, E_{d1}v \rangle`. Prove that $`S(v)` is a subrepresentation of $`V` isomorphic to $`k^d` (as a representation of $`\operatorname{Mat}_d(k)`), and that $`v \in S(v)`. Conclude that $`V = S(v_1) \oplus S(v_2) \oplus \cdots \oplus S(v_k)`, where $`\{v_1, v_2, \ldots, v_k\}` is a basis of $`E_{11}V`.

(c) Deduce Theorem 3.3.1.

## Formalization
%%%
tag := "Chapter3/Problem3.3.3/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Module.Pi.SimpleModules.auxiliaryRangeModule}

{Manual.docstring RepresentationTheory.Algebra.Module.Pi.SimpleModules.exists_equiv_pi_standardModule}

{Manual.docstring RepresentationTheory.Algebra.Module.Pi.SimpleModules.isSimpleModule_pi_iff_exists_simple_auxiliaryRange}

{Manual.docstring RepresentationTheory.Algebra.Module.Pi.SimpleModules.isSimpleModule_standardMatrixModule}

{Manual.docstring RepresentationTheory.Algebra.Module.Pi.SimpleModules.nonempty_equiv_standardModule_of_isSimpleModule}

{Manual.docstring RepresentationTheory.Algebra.Module.Pi.SimpleModules.single_one_mul_single_one}

{Manual.docstring RepresentationTheory.Algebra.Module.Pi.SimpleModules.sum_single_one}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.Matrix.ProductSemisimplicity.exists_linearEquiv_directSum_standardModules}

{Manual.docstring RepresentationTheory.Algebra.Matrix.ProductSemisimplicity.matrixProduct_simpleModule_classification}

{Manual.docstring RepresentationTheory.Algebra.Module.Pi.SimpleModules.IndexedAuxiliaryType.componentLinearEquivOfLinearEquiv}

{Manual.docstring RepresentationTheory.Algebra.Module.Pi.SimpleModules.IndexedAuxiliaryType.eq_index_of_linearEquiv}

{Manual.docstring RepresentationTheory.Algebra.Module.Pi.SimpleModules.IndexedAuxiliaryType.isSimpleModule_iff}

{Manual.docstring RepresentationTheory.Algebra.Module.Pi.SimpleModules.IndexedAuxiliaryType.linearEquivOfLinearEquiv}

{Manual.docstring RepresentationTheory.Algebra.Module.Pi.SimpleModules.exists_equiv_indexedAuxiliaryType_auxiliaryRange}

{Manual.docstring RepresentationTheory.Algebra.Module.Pi.SimpleModules.indexedAuxiliaryEndomorphism}
