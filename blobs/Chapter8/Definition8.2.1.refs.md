# References: Projective resolution

## Mathlib Coverage (exact)

- `CategoryTheory.ProjectiveResolution`

`CategoryTheory.ProjectiveResolution X` is a projective resolution of X in an abelian category.

## External Dependencies

- **Hom functor and its properties: Hom_A(M,N) as a vector space, left exactness, contravariance in first argument** (undergraduate_prerequisite)
  Mathlib (exact): `CategoryTheory.yoneda`, `CategoryTheory.coyoneda`, `LinearMap`
  Yoneda embedding provides the Hom functor abstractly. For modules, `LinearMap` (i.e., `M →ₗ[R] N`) is the Hom. Left exactness of Hom available.
- **Ext functors: definition as derived functors of Hom, long exact sequence in Ext, Ext^1 classifies extensions** (external_result)
  Mathlib (partial): `Ext`, `CategoryTheory.Abelian.Ext`, `CategoryTheory.ProjectiveResolution`, `CategoryTheory.ShortComplex.ShortExact.extClass`, `CategoryTheory.Abelian.Ext.contravariant_sequence_exact₂`
  Mathlib has two Ext APIs: the root `Ext` functor is constructed from projective resolutions, while `CategoryTheory.Abelian.Ext` is defined through the derived category and carries the long-exact-sequence and `ShortExact.extClass` APIs. These models are not identified here, and a full equivalence between extension classes and Ext^1 is not packaged.
  External source [natural_language]: Weibel, 'An Introduction to Homological Algebra' — Chapter 3
  External source [natural_language]: Rotman, 'An Introduction to Homological Algebra' — Chapters 6-7
