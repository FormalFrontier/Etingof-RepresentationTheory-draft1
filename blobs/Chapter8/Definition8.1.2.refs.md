# References: Projective module

## Mathlib Coverage (exact)

- `Module.Projective`

`Module.Projective R M` asserts that M is a projective R-module.

## External Dependencies

- **Modules over rings: left modules, right modules, submodules, quotient modules, free modules, simple modules** (undergraduate_prerequisite)
  Mathlib (exact): `Module`, `Submodule`, `Submodule.Quotient`, `Module.Free`, `IsSimpleModule`
  Full module theory. Mathlib uses left modules by convention. `IsSimpleModule` for simple modules. Free modules via `Module.Free`.
- **Exact sequences of modules: short exact sequences, left/right exactness of functors, splitting of exact sequences** (undergraduate_prerequisite)
  Mathlib (exact): `CategoryTheory.ShortComplex`, `CategoryTheory.ShortComplex.Exact`, `CategoryTheory.Limits.PreservesFiniteLimits`
  Short exact sequences via `ShortComplex` with `Exact` predicate. Left/right exactness via preservation of limits/colimits. Splitting available.
