/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter3.DiscussionProofOfTheorem331

#doc (Manual) "Proof of Theorem 3.3.1 using dual representations" =>
# Proof of Theorem 3.3.1 using dual representations
%%%
tag := "Chapter3/Discussion_proof_of_Theorem3.3.1"
number := false
%%%
**Proof of Theorem 3.3.1.** First, the given representations are clearly irreducible, since for any $`v \neq 0`, $`w \in V_i`, there exists $`a \in A` such that $`av = w`. Next, let $`X` be an $`n`-dimensional representation of $`A`. Then, $`X^*` is an $`n`-dimensional representation of $`A^{\mathrm{op}}`. But $`(\operatorname{Mat}_{d_i}(k))^{\mathrm{op}} \cong \operatorname{Mat}_{d_i}(k)` with isomorphism $`\varphi(X) = X^T`, as $`(BC)^T = C^T B^T`. Thus, $`A \cong A^{\mathrm{op}}` and $`X^*` may be viewed as an $`n`-dimensional representation of $`A`. Define

$$`\phi : \underbrace{A \oplus \cdots \oplus A}_{n \text{ copies}} \longrightarrow X^*`

by

$$`\phi(a_1, \ldots, a_n) = a_1 y_1 + \cdots + a_n y_n`

where $`\{y_i\}` is a basis of $`X^*`. The map $`\phi` is clearly surjective, as $`k \subset A`. Thus, the dual map $`\phi^* : X \longrightarrow A^{n*}` is injective. But $`A^{n*} \cong A^n` as representations of $`A` (check it!). Hence, $`\operatorname{Im} \phi^* \cong X` is a subrepresentation of $`A^n`. Next, $`\operatorname{Mat}_{d_i}(k) = d_i V_i`, so $`A = \bigoplus_{i=1}^r d_i V_i`, $`A^n = \bigoplus_{i=1}^r n d_i V_i`, as a representation of $`A`. Hence by Proposition 3.1.4, $`X = \bigoplus_{i=1}^r m_i V_i`, as desired. $`\square`

## Formalization
%%%
tag := "Chapter3/Discussion_proof_of_Theorem3.3.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Module.FiniteFamilySemisimplicity.auxiliaryLinearEquivDirectSumColumns}

{Manual.docstring RepresentationTheory.Algebra.Module.FiniteFamilySemisimplicity.dualPiLinearEquiv}

{Manual.docstring RepresentationTheory.Algebra.Module.FiniteFamilySemisimplicity.exists_linearEquiv_directSum_columnModules}

{Manual.docstring RepresentationTheory.Algebra.Module.FiniteFamilySemisimplicity.moduleDualOfRingEquivOpposite}

{Manual.docstring RepresentationTheory.Algebra.Module.FiniteFamilySemisimplicity.piAuxiliaryLinearEquivDirectSum}

{Manual.docstring RepresentationTheory.Algebra.Module.FiniteFamilySemisimplicity.ringEquivOpposite}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.Module.FiniteFamilySemisimplicity.auxiliaryLinearEquivDual}

{Manual.docstring RepresentationTheory.Algebra.Module.FiniteFamilySemisimplicity.basisLinearCombination}

{Manual.docstring RepresentationTheory.Algebra.Module.FiniteFamilySemisimplicity.basisLinearCombination_apply}

{Manual.docstring RepresentationTheory.Algebra.Module.FiniteFamilySemisimplicity.basisLinearCombination_surjective}

{Manual.docstring RepresentationTheory.Algebra.Module.FiniteFamilySemisimplicity.column_isSimpleModule}

{Manual.docstring RepresentationTheory.Algebra.Module.FiniteFamilySemisimplicity.dualPiLinearEquivPiDual}

{Manual.docstring RepresentationTheory.Algebra.Module.FiniteFamilySemisimplicity.matrixAlgEquivOpposite}

{Manual.docstring RepresentationTheory.Algebra.Module.FiniteFamilySemisimplicity.moduleDualMap}

{Manual.docstring RepresentationTheory.Algebra.Module.FiniteFamilySemisimplicity.moduleDualMap_injective_of_surjective}

{Manual.docstring RepresentationTheory.Algebra.Module.FiniteFamilySemisimplicity.moduleDualOfRingEquivOpposite_isScalarTower}

{Manual.docstring RepresentationTheory.Algebra.Module.FiniteFamilySemisimplicity.piOppositeRingEquiv}

{Manual.docstring RepresentationTheory.Algebra.Module.FiniteFamilySemisimplicity.toDoubleDualLinearEquiv}

{Manual.docstring RepresentationTheory.Algebra.Module.FiniteFamilySemisimplicity.toDualPiLinearMap}

{Manual.docstring RepresentationTheory.Algebra.Module.FiniteFamilySemisimplicity.toDualPiLinearMap_injective}

{Manual.docstring RepresentationTheory.Algebra.Module.IsotypicDecomposition.exists_equiv_directSum_fin}
