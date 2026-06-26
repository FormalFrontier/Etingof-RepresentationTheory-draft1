import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Jacobson.Semiprimary
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Algebra.Tower

/-!
# Finite-dimensional algebras are semiprimary

A finite-dimensional algebra `A` over a field `k` is a left Artinian ring, hence
**semiprimary**: its Jacobson radical `Ring.jacobson A` is nilpotent and the quotient
`A ⧸ Ring.jacobson A` is semisimple (`Mathlib.RingTheory.Jacobson.Semiprimary`).

This is the foundational ring-theoretic layer for the Bass route to Example 8.1.7
(`projective ⟺ injective dual`): over a left perfect — a fortiori semiprimary — ring,
every flat left module is projective. The flat-⟹-projective theorem itself is the
substantial remaining piece (Bass's characterization of perfect rings); see issue #5476.

## Main results

* `isArtinianRing_of_finiteDimensional`: a finite-dimensional `k`-algebra is a left
  Artinian ring.
* `isSemiprimaryRing_of_finiteDimensional`: a finite-dimensional `k`-algebra is semiprimary.

Both are stated as `theorem`s rather than `instance`s because the field `k` does not appear
in the conclusion (`IsArtinianRing A` / `IsSemiprimaryRing A`), so type-class search cannot
recover it; downstream users supply `k` explicitly via `haveI := ... k A`.
-/

/-- A finite-dimensional algebra over a field is a left Artinian ring.

The left ideals of `A` are in particular `k`-subspaces, and a finite-dimensional vector space
satisfies the descending chain condition on subspaces; `isArtinian_of_tower` transports the
Artinian property along the scalar tower `k → A → A`. -/
theorem isArtinianRing_of_finiteDimensional
    (k A : Type*) [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] :
    IsArtinianRing A :=
  isArtinian_of_tower k inferInstance

/-- A finite-dimensional algebra over a field is semiprimary: its Jacobson radical is
nilpotent and the quotient by the Jacobson radical is semisimple.

This is immediate from `isArtinianRing_of_finiteDimensional` together with Mathlib's instance
that every left Artinian ring is semiprimary. -/
theorem isSemiprimaryRing_of_finiteDimensional
    (k A : Type*) [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] :
    IsSemiprimaryRing A :=
  haveI : IsArtinianRing A := isArtinianRing_of_finiteDimensional k A
  inferInstance
