/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter2.Example292

#doc (Manual) "Examples of Lie algebras" =>
# Examples of Lie algebras
%%%
tag := "Chapter2/Example2.9.2"
number := false
%%%
**Example 2.9.2.** Some examples of Lie algebras are:

(1) Any space $`\mathfrak{g}` with $`[\ ,\ ] = 0` (abelian Lie algebra).

(2) Any associative algebra $`A` with $`[a, b] = ab - ba`, in particular, the endomorphism algebra $`A = \operatorname{End}(V)`, where $`V` is a vector space. When such an $`A` is regarded as a Lie algebra, it is often denoted by $`\mathfrak{gl}(V)` (general linear Lie algebra).

(3) Any subspace $`U` of an associative algebra $`A` such that $`[a, b] \in U` for all $`a, b \in U`.

(4) The space $`\operatorname{Der}(A)` of derivations of an algebra $`A`, i.e. linear maps $`D : A \to A` which satisfy the Leibniz rule:

$$`D(ab) = D(a)b + aD(b).`

## Formalization
%%%
tag := "Chapter2/Example2.9.2/formalization"
number := false
%%%

### Primary declarations

{Manual.docstring RepresentationTheory.Algebra.Lie.Constructions.derivationLieSubalgebra}

{Manual.docstring RepresentationTheory.Algebra.Lie.Constructions.mem_derivationLieSubalgebra_iff}

### Supporting declarations

{Manual.docstring RepresentationTheory.Algebra.Lie.Constructions.AbelianLieAlgebra}

{Manual.docstring RepresentationTheory.Algebra.Lie.Constructions.AbelianLieAlgebra.instLieAlgebra}

{Manual.docstring RepresentationTheory.Algebra.Lie.Constructions.AbelianLieAlgebra.instLieRing}

{Manual.docstring RepresentationTheory.Algebra.Lie.Constructions.AbelianLieAlgebra.isLieAbelian}

{Manual.docstring RepresentationTheory.Algebra.Lie.Constructions.IsDerivation}

{Manual.docstring RepresentationTheory.Algebra.Lie.Constructions.commutatorLieRing}

{Manual.docstring RepresentationTheory.Algebra.Lie.Constructions.derivationLieEquiv}

{Manual.docstring RepresentationTheory.Algebra.Lie.Constructions.derivationLieSubalgebra.bracket_apply}

{Manual.docstring RepresentationTheory.Algebra.Lie.Constructions.derivationLieSubalgebra.leibniz}

{Manual.docstring RepresentationTheory.Algebra.Lie.Constructions.endomorphismLieAlgebra}

{Manual.docstring RepresentationTheory.Algebra.Lie.Constructions.subalgebraLieAlgebra}
