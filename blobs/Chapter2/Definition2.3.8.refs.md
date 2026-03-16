# References: Indecomposable representation

## Mathlib Coverage (partial)

- `Indecomposable`

Mathlib has `Indecomposable` for order theory. For modules, indecomposability (not expressible as direct sum of proper submodules) may need to be defined using `IsNontrivial` and non-existence of complementary submodule pairs. Partial coverage.

## External Sources (definition gap)

- **[natural_language]** Etingof et al., 'Introduction to Representation Theory' — Definition 2.3.8 and surrounding discussion
  The book itself provides the definition; formalization requires defining indecomposability for modules as non-existence of complementary submodule decomposition
- **[other_formal]** MathComp (Coq) — mathcomp-analysis and mathcomp-ssreflect have module decomposition infrastructure
  Coq's approach to direct sum decomposition may guide the Lean formalization of indecomposable modules
