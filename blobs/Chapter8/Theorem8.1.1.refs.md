# References: Equivalent characterizations of projective modules

## External Dependencies

- **Modules over rings: left modules, right modules, submodules, quotient modules, free modules, simple modules** (undergraduate_prerequisite)
  Mathlib (exact): `Module`, `Submodule`, `Submodule.Quotient`, `Module.Free`, `IsSimpleModule`
  Full module theory. Mathlib uses left modules by convention. `IsSimpleModule` for simple modules. Free modules via `Module.Free`.
- **Exact sequences of modules: short exact sequences, left/right exactness of functors, splitting of exact sequences** (undergraduate_prerequisite)
  Mathlib (exact): `CategoryTheory.ShortComplex`, `CategoryTheory.ShortComplex.Exact`, `CategoryTheory.Limits.PreservesFiniteLimits`
  Short exact sequences via `ShortComplex` with `Exact` predicate. Left/right exactness via preservation of limits/colimits. Splitting available.
- **Hom functor and its properties: Hom_A(M,N) as a vector space, left exactness, contravariance in first argument** (undergraduate_prerequisite)
  Mathlib (exact): `CategoryTheory.yoneda`, `CategoryTheory.coyoneda`, `LinearMap`
  Yoneda embedding provides the Hom functor abstractly. For modules, `LinearMap` (i.e., `M →ₗ[R] N`) is the Hom. Left exactness of Hom available.
- **Every module over a ring is a quotient of a free module (existence of free resolutions)** (folklore)
  Mathlib (partial): `Module.Free`, `Submodule.Quotient`
  Free modules and quotients exist. The statement that every module is a quotient of a free module is a standard construction (take generators, map from a free module). Projective resolutions available via `CategoryTheory.ProjectiveResolution`.
