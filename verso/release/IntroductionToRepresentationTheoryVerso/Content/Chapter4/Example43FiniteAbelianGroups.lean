/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter4.Example43FiniteAbelianGroups

#doc (Manual) "Representations of finite abelian groups and dual groups" =>

# Representations of finite abelian groups and dual groups
%%%
tag := "Chapter4/Example4.3_FiniteAbelianGroups"
number := false
%%%
(1) Finite abelian groups $`G = \mathbb{Z}_{n_1} \times \cdots \times \mathbb{Z}_{n_k}`. Let $`G^\vee` be the set of irreducible representations of $`G`. Every element of $`G` forms a conjugacy class, so $`|G^\vee| = |G|`. Recall that all irreducible representations over $`\mathbb{C}` (and algebraically closed fields in general) of commutative algebras and groups are 1-dimensional. Thus, $`G^\vee` is an abelian group: if $`\rho_1, \rho_2 : G \to \mathbb{C}^\times` are irreducible representations, then so are the representations $`\rho_1(g)\rho_2(g)` and $`\rho_1(g)^{-1}`. The group $`G^\vee` is called the **dual group** or **character group** of $`G`.

For given $`n \geq 1`, define $`\rho : \mathbb{Z}_n \to \mathbb{C}^\times` by $`\rho(m) = e^{2\pi i m/n}`. Then $`\mathbb{Z}_n^\vee = \{\rho^k : k = 0, \ldots, n - 1\}`, so $`\mathbb{Z}_n^\vee \cong \mathbb{Z}_n`. In general,

$$`(G_1 \times G_2 \times \cdots \times G_n)^\vee = G_1^\vee \times G_2^\vee \times \cdots \times G_n^\vee,`
so $`G^\vee \cong G` for any finite abelian group $`G`. This isomorphism is, however, noncanonical: the particular decomposition of $`G` as $`\mathbb{Z}_{n_1} \times \cdots \times \mathbb{Z}_{n_k}` is not unique as far as which elements of $`G` correspond to $`\mathbb{Z}_{n_1}`, etc., is concerned. On the other hand, $`G \cong (G^\vee)^\vee` is a canonical isomorphism, given by $`\varphi : G \to (G^\vee)^\vee`, where $`\varphi(g)(\chi) = \chi(g)`.

## Formalization
%%%
tag := "Chapter4/Example4.3_FiniteAbelianGroups/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Group.CharacterDuality.characterGroupPiEquiv}

{Manual.docstring RepresentationTheory.Group.CharacterDuality.characterGroupProdEquiv}

{Manual.docstring RepresentationTheory.Group.CharacterDuality.finrank_eq_one_of_isSimpleModule}

### Supporting declarations

{Manual.docstring RepresentationTheory.Group.CharacterDuality.characterGroup}

{Manual.docstring RepresentationTheory.Group.CharacterDuality.characterGroupDualEquiv}

{Manual.docstring RepresentationTheory.Group.CharacterDuality.characterGroupDualEquiv_apply}

{Manual.docstring RepresentationTheory.Group.CharacterDuality.nonempty_characterGroupEquiv}
