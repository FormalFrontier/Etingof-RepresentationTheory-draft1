# References: Character vanishes or element acts as scalar when gcd(|C|, dim V) = 1

## External Dependencies

- **Algebraic integers and algebraic number theory basics: algebraic integers form a ring, norm of algebraic integers** (undergraduate_prerequisite)
  Mathlib (exact): `IsIntegral`, `NumberField.RingOfIntegers`, `Algebra.norm`
  `IsIntegral R x` for algebraic elements. `NumberField.RingOfIntegers` for the ring of integers. `Algebra.norm` for the norm map.
- **Complex analysis basics: roots of unity, absolute values of complex numbers, triangle inequality for sums of roots of unity** (undergraduate_prerequisite)
  Mathlib (exact): `IsPrimitiveRoot`, `rootsOfUnity`, `Complex.normSq`, `Complex.instNorm`
  Roots of unity via `IsPrimitiveRoot` and `rootsOfUnity`. Complex absolute value via the norm instance `Complex.instNorm` (using `‖z‖`). Triangle inequality available through the normed field instance.
