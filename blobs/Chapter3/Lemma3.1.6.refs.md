# References: Surjective map from direct sum of irreducibles splits

## External Dependencies

- **Vector spaces over a field: definition, dimension, subspaces, quotient spaces, direct sums, bases** (undergraduate_prerequisite)
  Mathlib (exact): `Module`, `FiniteDimensional`, `Module.finrank`, `Submodule`, `Submodule.Quotient`, `DirectSum`, `Basis`
  Vector spaces are modeled as `Module k V` where `k` is a `Field`. Dimension via `Module.finrank`. Full support for subspaces, quotients, direct sums, and bases.
- **Zorn's lemma: every partially ordered set in which every chain has an upper bound has a maximal element** (external_result)
  Mathlib (exact): `zorn_le`
  `zorn_le` states Zorn's lemma for preorders. Also available: `zorn_partialOrder`, `zorn_nonempty_preorder`.
