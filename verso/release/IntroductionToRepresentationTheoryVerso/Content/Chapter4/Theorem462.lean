/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter4.Theorem462

#doc (Manual) "Existence and uniqueness of unitary structure for finite groups" =>

# Existence and uniqueness of unitary structure for finite groups
%%%
tag := "Chapter4/Theorem4.6.2"
number := false
%%%

**Theorem 4.6.2.** _If $`G` is finite, then any finite dimensional representation of $`G` has a unitary structure. If the representation is irreducible, this structure is unique up to scaling by a positive real number._

**Proof.** Take any positive definite Hermitian form $`B` on $`V` and define another Hermitian form $`\mathbf{B}` on $`V` as follows:

$$`\mathbf{B}(v, w) = \sum_{g \in G} B(\rho_V(g)v, \rho_V(g)w).`

Then $`\mathbf{B}` is a positive definite $`G`-invariant Hermitian form on $`V`.

If $`V` is an irreducible representation and $`B_1, B_2` are two positive definite $`G`-invariant Hermitian forms on $`V`, then $`B_1(v, w) = B_2(Av, w)` for some linear map $`A : V \to V` (since any positive definite Hermitian form is nondegenerate), and moreover $`A` is also $`G`-invariant, i.e., is a homomorphism of representations. Then by Schur's lemma, $`A = \lambda \mathrm{Id}`, and clearly $`\lambda > 0`. $`\square`

## Formalization
%%%
tag := "Chapter4/Theorem4.6.2/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.Complex.InvariantInnerProduct.Representation.auxiliaryInvariantInnerProductResult}

{Manual.docstring RepresentationTheory.Complex.InvariantInnerProduct.Representation.exists_invariantInnerProductCore}
