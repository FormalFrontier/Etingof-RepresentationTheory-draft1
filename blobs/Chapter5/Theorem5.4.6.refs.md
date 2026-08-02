# References: Group with conjugacy class of size p^k is not simple

## External Dependencies

- **Groups: definition, subgroups, normal subgroups, quotient groups, group homomorphisms, group actions, conjugacy classes, center of a group** (undergraduate_prerequisite)
  Mathlib (exact): `Group`, `Subgroup`, `Subgroup.Normal`, `QuotientGroup.mk'`, `MonoidHom`, `MulAction`, `ConjClasses`, `Subgroup.center`
  Comprehensive group theory. All listed concepts have direct Mathlib counterparts.
- **Algebraic integers and algebraic number theory basics: algebraic integers form a ring, norm of algebraic integers** (undergraduate_prerequisite)
  Mathlib (exact): `IsIntegral`, `NumberField.RingOfIntegers`, `Algebra.norm`
  `IsIntegral R x` for algebraic elements. `NumberField.RingOfIntegers` for the ring of integers. `Algebra.norm` for the norm map.
- **Generalized Schur orthogonality relations: orthogonality of matrix coefficients of irreducible representations over compact or finite groups** (folklore)
  Mathlib (partial): `FDRep.character`, `FDRep.char_orthonormal`, `FDRep.average_char_eq_finrank_invariants`
  `FDRep.char_orthonormal` proves irreducible-character orthonormality for finite groups, and `FDRep.average_char_eq_finrank_invariants` supplies the averaging identity. General matrix-coefficient orthogonality, especially for compact groups, is not packaged.
