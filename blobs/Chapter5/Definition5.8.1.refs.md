# References: Induced representation Ind_H^G V

## Mathlib Coverage (exact)

- `Representation`
- `MonoidAlgebra`
- `TensorProduct`

Mathlib has `Representation k G V` for group representations and `MonoidAlgebra k G` for group algebras. The induced representation `Ind_H^G V = k[G] ⊗[k[H]] V` can be constructed from these components. A dedicated `Representation.induced` may not exist but the building blocks are available.

## External Dependencies

- **Frobenius reciprocity: Hom_G(Ind_H^G V, W) ≅ Hom_H(V, Res_H W) naturally** (external_result)
  Mathlib (missing): `Representation`, `Representation.linHom`, `Representation.ofMulAction`
  Representation theory infrastructure exists but Frobenius reciprocity (adjunction between induction and restriction) is NOT stated in Mathlib. Induction and restriction functors would need to be defined and the adjunction proved.
