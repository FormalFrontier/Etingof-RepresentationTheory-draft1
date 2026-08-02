# References: Existence and uniqueness of unitary structure for finite groups

## External Dependencies

- **Characters of representations are class functions; character of a direct sum is sum of characters; character of a tensor product is product of characters** (folklore)
  Mathlib (partial): `FDRep.character`, `FDRep.char_conj`, `FDRep.char_tensor`
  `FDRep.char_conj` proves the class-function property and `FDRep.char_tensor` proves tensor multiplicativity. A general direct-sum additivity theorem is not packaged in Mathlib, so that remaining clause is supplied in the project.
  External source [natural_language]: Serre, 'Linear Representations of Finite Groups' — Section 2.1
  External source [other_formal]: MathComp (Coq) — character.v, classfun.v
