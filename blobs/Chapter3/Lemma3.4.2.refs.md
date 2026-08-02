# References: Existence of filtration with irreducible successive quotients

## External Dependencies

- **Rings and ideals: definition of rings, two-sided ideals, quotient rings, nilpotent ideals, Jacobson radical** (undergraduate_prerequisite)
  Mathlib (exact): `Ring`, `Ideal`, `Ideal.Quotient.mk`, `IsNilpotent`, `Ideal.jacobson`
  Complete ring theory. `IsNilpotent` for elements; nilpotent ideals expressible as `∀ x ∈ I, IsNilpotent x` or via `I ^ n = ⊥`. Jacobson radical via `Ideal.jacobson`.
- **Nilpotent ideals and nilpotency: a nilpotent ideal I satisfies I^n = 0 for some n; properties of nilpotent elements in algebras** (folklore)
  Mathlib (partial): `IsNilpotent`, `Ideal.IsNilpotent.induction_on`, `IsArtinianRing.isNilpotent_jacobson_bot`
  `IsNilpotent I` expresses nilpotence by ideal powers and the Artinian Jacobson radical is proved nilpotent for arbitrary rings. `Ideal.IsNilpotent.induction_on` is restricted to commutative rings; a comparable two-sided nilpotent-ideal API for the book's noncommutative algebras is absent.
  External source [natural_language]: Lam, 'A First Course in Noncommutative Rings' — Chapter 2
