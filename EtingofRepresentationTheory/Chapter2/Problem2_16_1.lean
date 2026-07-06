import Mathlib

/-!
# Problem 2.16.1: Lie's theorem

The **commutant** `K(𝔤)` of a Lie algebra `𝔤` is the linear span of the elements `[x, y]`; it is
an ideal in `𝔤`. A finite dimensional Lie algebra `𝔤` is **solvable** if `Kⁿ(𝔤) = 0` for some `n`.
**Lie's theorem:** if `k = ℂ` and `V` is a finite dimensional irreducible representation of a
solvable Lie algebra `𝔤`, then `V` is 1-dimensional.

## Formalization

Solvability is Mathlib's `LieAlgebra.IsSolvable` (defined via the derived series, matching the
`Kⁿ(𝔤) = 0` condition). A representation of `𝔤` is a `LieModule`; irreducibility ("the only
subrepresentations are `0` and `V`") is `IsSimpleOrder (LieSubmodule ℂ 𝔤 V)`. The conclusion
"`V` is 1-dimensional" is `Module.finrank ℂ V = 1`.

This is the **statement pass**: the statement is recorded with a `sorry` proof.
-/

namespace Etingof.Problem2_16_1

open Module (finrank)

variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule L V] [LieModule ℂ L V]

/-- **Problem 2.16.1 (Lie's theorem).** A finite dimensional irreducible representation `V` of a
solvable complex Lie algebra `L` is one-dimensional. -/
theorem finrank_eq_one_of_isSolvable [LieAlgebra.IsSolvable L]
    [FiniteDimensional ℂ V] [Nontrivial V] (hirr : IsSimpleOrder (LieSubmodule ℂ L V)) :
    finrank ℂ V = 1 := by
  sorry

end Etingof.Problem2_16_1
