import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.CharP.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Problem 2.16.4: Irreducible representations of `𝔰𝔩(2)` in characteristic `p > 2`

Over an algebraically closed field `k` of characteristic `p > 2`, the irreducible finite
dimensional representations of `𝔰𝔩(2, k)` are constrained very differently from characteristic
`0` (where they are the `(n+1)`-dimensional modules `L(n)`, `n ≥ 0`, of unbounded dimension).

The central feature of the characteristic-`p` classification is the **dimension bound**: every
irreducible representation of `𝔰𝔩(2, k)` has dimension **at most `p`**, and this bound is
achieved. (The fine classification parametrizes the irreducibles by a highest weight `λ ∈ k`
together with, for the non-restricted ones, extra data; that full parametrization requires
highest-weight-module infrastructure and is deferred. Here we record the sharp dimension bound,
which is the crisp universally-true part of the answer.)

We realize `𝔰𝔩(2, k)` as Mathlib's `LieAlgebra.SpecialLinear.sl (Fin 2) k`. Statement-only.
-/

namespace Etingof.Problem2_16_4

open scoped Matrix

-- `LieRing.ofAssociativeRing` is a local instance from Mathlib v4.31 onward; re-enable locally.
attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type*) [Field k]

/-- The Lie algebra `𝔰𝔩(2, k)` of traceless `2 × 2` matrices. -/
noncomputable def sl2 : LieSubalgebra k (Matrix (Fin 2) (Fin 2) k) :=
  LieAlgebra.SpecialLinear.sl (Fin 2) k

/-- **Dimension bound.** Over an algebraically closed field of characteristic `p > 2`, every
irreducible finite dimensional representation of `𝔰𝔩(2)` has dimension at most `p`. -/
theorem finrank_irreducible_le_char [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hp : 2 < p)
    (M : Type*) [AddCommGroup M] [Module k M] [LieRingModule (sl2 k) M] [LieModule k (sl2 k) M]
    [FiniteDimensional k M] [LieModule.IsIrreducible k (sl2 k) M] :
    Module.finrank k M ≤ p :=
  sorry

/-- **The bound is sharp.** There exist irreducible representations of dimension `p`: it is not the
case that every irreducible finite dimensional representation has dimension `< p`. -/
theorem exists_irreducible_dim_char [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hp : 2 < p) :
    ¬ ∀ (M : Type) [AddCommGroup M] [Module k M] [LieRingModule (sl2 k) M]
        [LieModule k (sl2 k) M] [FiniteDimensional k M] [LieModule.IsIrreducible k (sl2 k) M],
        Module.finrank k M < p :=
  sorry

end Etingof.Problem2_16_4
