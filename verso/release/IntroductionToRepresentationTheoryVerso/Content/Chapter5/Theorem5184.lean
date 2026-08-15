/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter5.Theorem5184

#doc (Manual) "Schur-Weyl duality: V^\\{\u2297n\\} = \u2295 V\\_lambda \u2297 L\\_lambda" =>

# Schur-Weyl duality: V^\{⊗n\} = ⊕ V\_lambda ⊗ L\_lambda
%%%
tag := "Chapter5/Theorem5.18.4"
number := false
%%%

*Theorem 5.18.4.* _(i) The image $`A` of $`k[S_n]` and the image $`B` of $`\mathcal{U}(\mathfrak{gl}(V))` in $`\operatorname{End}(V^{\otimes n})` are centralizers of each other._

_(ii) Both $`A` and $`B` are semisimple. In particular, $`V^{\otimes n}` is a semisimple $`\mathfrak{gl}(V)`-module._

_(iii) We have a decomposition of $`(A \otimes B)`-modules_

$$`V^{\otimes n} = \bigoplus_{\lambda} V_{\lambda} \otimes L_{\lambda},`

_where the summation is taken over partitions of $`n`, $`V_{\lambda}` are Specht modules for $`S_n`, and $`L_{\lambda}` are some distinct irreducible representations of $`\mathfrak{gl}(V)` or zero._

## Formalization
%%%
tag := "Chapter5/Theorem5.18.4/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Auxiliary.MutualCentralizers.mutual_centralizer_algebras}

### Supporting declarations

{Manual.docstring RepresentationTheory.Auxiliary.MutualCentralizers.associatedSubalgebras_semisimple}

{Manual.docstring RepresentationTheory.Auxiliary.MutualCentralizers.exists_auxiliarySpace_decomposition_with_compatibility}

{Manual.docstring RepresentationTheory.Auxiliary.TensorDecomposition.existsAuxiliaryDirectSumTensorProductDecomposition}
