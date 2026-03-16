# References: Dual representation

## Mathlib Coverage (exact)

- `Module.Dual`
- `Representation.dual`

`Module.Dual R M` is the dual vector space. For group representations, `Representation.dual` gives the contragredient.

## External Dependencies

- **Matrix algebra: matrix multiplication, trace, determinant, similarity, matrix units** (undergraduate_prerequisite)
  Mathlib (exact): `Matrix`, `Matrix.mul`, `Matrix.trace`, `Matrix.det`, `Matrix.StdBasisMatrix`, `Matrix.trace_mul_comm`
  Full matrix algebra. `Matrix.StdBasisMatrix` provides matrix units. `Matrix.trace_mul_comm` gives tr(AB) = tr(BA).
