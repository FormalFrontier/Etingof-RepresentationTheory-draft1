# References: Full subcategory

## Mathlib Coverage (exact)

- `CategoryTheory.InducedCategory`
- `CategoryTheory.Functor.Full`

`InducedCategory D F` gives a category on a type C induced by a function F : C → D. A full subcategory is modeled by combining `InducedCategory` with `Functor.Full` (the property that the functor on Hom sets is surjective).

## External Dependencies

- **Category theory basics assumed in Chapter 7: sets, functions, composition, associativity (for motivating examples)** (undergraduate_prerequisite)
  Mathlib (exact): `CategoryTheory.Category`, `CategoryTheory.Functor`
  Comprehensive category theory library. `CategoryTheory.Category` and `CategoryTheory.Functor` are the core types.
