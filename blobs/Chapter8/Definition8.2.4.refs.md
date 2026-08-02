# References: Ext functors

## Mathlib Coverage (exact)

- `Ext`

Mathlib has `Ext R M N` for Ext groups, defined via derived functors of Hom.

## External Dependencies

- **Ext functors: definition as derived functors of Hom, long exact sequence in Ext, Ext^1 classifies extensions** (external_result)
  Mathlib (partial): `Ext`, `CategoryTheory.Abelian.Ext`, `CategoryTheory.ProjectiveResolution`, `CategoryTheory.ShortComplex.ShortExact.extClass`, `CategoryTheory.Abelian.Ext.contravariant_sequence_exact₂`
  Mathlib has two Ext APIs: the root `Ext` functor is constructed from projective resolutions, while `CategoryTheory.Abelian.Ext` is defined through the derived category and carries the long-exact-sequence and `ShortExact.extClass` APIs. These models are not identified here, and a full equivalence between extension classes and Ext^1 is not packaged.
  External source [natural_language]: Weibel, 'An Introduction to Homological Algebra' — Chapter 3
  External source [natural_language]: Rotman, 'An Introduction to Homological Algebra' — Chapters 6-7
