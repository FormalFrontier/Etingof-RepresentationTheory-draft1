/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter4.Theorem411

#doc (Manual) "Maschke's theorem" =>

# Maschke's theorem
%%%
tag := "Chapter4/Theorem4.1.1"
number := false
%%%
**Theorem 4.1.1** (Maschke). _Let $`G` be a finite group and let $`k` be a field whose characteristic does not divide $`|G|`. Then:_

_(i) The algebra $`k[G]` is semisimple._

_(ii) There is an isomorphism of algebras $`\psi : k[G] \to \bigoplus_i \operatorname{End} V_i` defined by $`g \mapsto \bigoplus_i g|_{V_i}`, where $`V_i` are the irreducible representations of $`G`. In particular, this is an isomorphism of representations of $`G` (where $`G` acts on both sides by left multiplication). Hence, the regular representation $`k[G]` decomposes into irreducibles as $`\bigoplus_i \dim(V_i) V_i`, and one has the "sum of squares formula"_

$$`|G| = \sum_i \dim(V_i)^2.`
**Proof.** By Proposition 3.5.8, (i) implies (ii), and to prove (i), it is sufficient to show that if $`V` is a finite dimensional representation of $`G` and $`W \subset V` is any subrepresentation, then there exists a subrepresentation $`W' \subset V` such that $`V = W \oplus W'` as representations.

Choose any complement $`\widehat{W}` of $`W` in $`V`. (Thus $`V = W \oplus \widehat{W}` as _vector spaces_, but not necessarily as _representations_.) Let $`P` be the projection along $`\widehat{W}` onto $`W`, i.e., the operator on $`V` defined by $`P|_W = \operatorname{Id}` and $`P|_{\widehat{W}} = 0`. Let

$$`\overline{P} := \frac{1}{|G|} \sum_{g \in G} \rho(g) P \rho(g^{-1}),`

where $`\rho(g)` is the action of $`g` on $`V`, and let

$$`W' = \ker \overline{P}.`

Now $`\overline{P}|_W = \operatorname{Id}` and $`\overline{P}(V) \subseteq W`, so $`\overline{P}^2 = \overline{P}`, and so $`\overline{P}` is a projection along $`W'`. Thus, $`V = W \oplus W'` as vector spaces.

Moreover, for any $`h \in G` and any $`y \in W'`,

$$`\overline{P}\rho(h)y = \frac{1}{|G|} \sum_{g \in G} \rho(g) P \rho(g^{-1}h) y`

$$`= \frac{1}{|G|} \sum_{\ell \in G} \rho(h\ell) P \rho(\ell^{-1}) y = \rho(h) \overline{P} y = 0,`

so $`\rho(h)y \in \ker \overline{P} = W'`. Thus, $`W'` is invariant under the action of $`G` and is therefore a subrepresentation of $`V`. Thus, $`V = W \oplus W'` is the desired decomposition into subrepresentations. $`\square`

## Formalization
%%%
tag := "Chapter4/Theorem4.1.1/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Semisimplicity.FiniteDimensional.finiteDimensional_tfae}

{Manual.docstring RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.auxiliaryMap_apply_single}

{Manual.docstring RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.groupAlgebraEquivRepresentationEnd}

{Manual.docstring RepresentationTheory.FiniteGroup.RegularRepresentationDecomposition.FiniteGroup.exists_complete_simple_family_coordinateRepresentation}

{Manual.docstring RepresentationTheory.FiniteGroup.RegularRepresentationDecomposition.FiniteGroup.exists_complete_simple_family_with_groupAlgebra_equiv}

### Supporting declarations

{Manual.docstring RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.auxiliaryFDRepIsoAuxiliary}

{Manual.docstring RepresentationTheory.FDRep.GroupAlgebraDecomposition.DecompositionData.auxiliaryFDRepIsoAuxiliaryPrime}

{Manual.docstring RepresentationTheory.FiniteGroup.RegularRepresentationDecomposition.FiniteGroup.exists_complete_simple_family_endomorphismRepresentation}

{Manual.docstring RepresentationTheory.FiniteGroup.RegularRepresentationDecomposition.FiniteGroup.exists_positive_dimensions_sum_sq_eq_card}

{Manual.docstring RepresentationTheory.FiniteGroup.RegularRepresentationDecomposition.MonoidAlgebra.isSemisimpleRing_of_isUnit_card}
