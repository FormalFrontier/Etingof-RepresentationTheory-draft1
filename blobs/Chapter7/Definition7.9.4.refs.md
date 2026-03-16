# References: Semisimple abelian category

## Mathlib Coverage (partial)

- `CategoryTheory.Abelian`

Mathlib has abelian categories but does not have a dedicated `IsSemisimple` predicate for categories (every object is semisimple). For module categories, `IsSemisimpleRing` implies the category is semisimple.

## External Sources (definition gap)

- **[natural_language]** Etingof et al., 'Tensor Categories' (AMS Mathematical Surveys, 2015) — Chapter 1
  Semisimple categories defined; relationship to semisimple algebras and module categories

## External Dependencies

- **Abelian categories: kernels, cokernels, exact sequences in abstract categorical setting** (undergraduate_prerequisite)
  Mathlib (exact): `CategoryTheory.Abelian`, `CategoryTheory.Limits.kernel`, `CategoryTheory.Limits.cokernel`
  Comprehensive abelian category library. Kernels, cokernels, exact sequences, diagram lemmas all present.
