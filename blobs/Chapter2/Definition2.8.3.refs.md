# References: Representation of a quiver

## Mathlib Coverage (partial)

- `Representation`
- `CategoryTheory.Functor`

Mathlib has `Representation k G V` for group representations. Quiver representations can be modeled as functors from the free category on the quiver to `ModuleCat k`. Specific quiver representation API exists but naming may vary.

## External Sources (definition gap)

- **[natural_language]** Schiffler, 'Quiver Representations' (Springer, 2014) — Chapter 2
  Comprehensive treatment of quiver representations as functors from path categories to vector spaces; detailed constructions suitable for formalization
- **[natural_language]** Assem, Simson, Skowroński, 'Elements of the Representation Theory of Associative Algebras, Vol. 1' — Chapter III
  Detailed development of quiver representations with explicit constructions
- **[other_formal]** Coq UniMath — CategoryTheory library has functor categories that model quiver representations
  Demonstrates how to model quiver representations via functors in a proof assistant
