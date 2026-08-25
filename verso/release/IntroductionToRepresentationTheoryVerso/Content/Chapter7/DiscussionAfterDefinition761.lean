/-
Copyright (c) 2026 American Mathematical Society. All rights reserved.
-/

import VersoManual
import RepresentationTheory

open Verso.Genre Manual

namespace IntroductionToRepresentationTheoryVerso.Content.Chapter7.DiscussionAfterDefinition761

#doc (Manual) "Uniqueness of adjoints and analogy with linear algebra" =>

# Uniqueness of adjoints and analogy with linear algebra
%%%
tag := "Chapter7/Discussion_after_Definition7.6.1"
number := false
%%%

Not every functor has a left or right adjoint, but if it does, it is unique and can be constructed canonically (i.e., if we somehow found two such functors, then there is a canonical isomorphism between them). This follows easily from the Yoneda lemma, since if
*Table 1.* Dictionary between category theory and linear algebra.

:::table +header
*
  * Category theory
  * Linear algebra
*
  * Category $`\mathcal{C}`
  * Vector space $`V` with a nondegenerate inner product
*
  * The set of morphisms $`\operatorname{Hom}(X, Y)`
  * Inner product $`(x, y)` on $`V` (maybe nonsymmetric)
*
  * Opposite category $`\mathcal{C}^{\mathrm{op}}`
  * Same space $`V` with reversed inner product
*
  *
    The category *Sets*
  * The ground field $`k`
*
  * Full subcategory in $`\mathcal{C}`
  * Nondegenerate subspace in $`V`
*
  * Functor $`F : \mathcal{C} \to \mathcal{D}`
  * Linear operator $`f : V \to W`
*
  * Functor $`F : \mathcal{C} \to \mathbf{Sets}`
  * Linear functional $`f \in V^* = \operatorname{Hom}(V, k)`
*
  * Representable functor
  * Linear functional $`f \in V^*` given by $`f(v) = (u, v)`, $`u \in V`
*
  * Yoneda lemma
  * Nondegeneracy of the inner product (on both sides)
*
  * Not all functors are representable
  * If $`\dim V = \infty`, not $`\forall f \in V^*`, $`f(v) = (u, v)`
*
  * Left and right adjoint functors
  * Left and right adjoint operators
*
  * Adjoint functors don't always exist
  * Adjoint operators may not exist if $`\dim V = \infty`
*
  * If they do, they are unique
  * If they do, they are unique
*
  * Left and right adjoints may not coincide
  * The inner product may be nonsymmetric
:::

$`F, G` are a pair of adjoint functors, then $`F(X)` represents the functor $`Y \mapsto \operatorname{Hom}(X, G(Y))` and $`G(Y)` represents the functor $`X \mapsto \operatorname{Hom}(F(X), Y)`.

## Formalization
%%%
tag := "Chapter7/Discussion_after_Definition7.6.1/formalization"
number := false
%%%

### Supporting declarations

{Manual.docstring RepresentationTheory.CategoryTheory.Adjunction.Representability.corepresentableBy}

{Manual.docstring RepresentationTheory.CategoryTheory.Adjunction.Representability.representableBy}
