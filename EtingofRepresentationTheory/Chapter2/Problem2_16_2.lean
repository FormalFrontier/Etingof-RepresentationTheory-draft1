import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.CharP.Basic

/-!
# Problem 2.16.2: Irreducible representations of the 2-dimensional Lie algebra `[X, Y] = Y`

Let `𝔤` be the two-dimensional Lie algebra with basis `X, Y` and commutation relation
`[X, Y] = Y`. We realize it as the Lie subalgebra of `𝔤𝔩(2, k)` spanned by the matrix units
`X = e₁₁` and `Y = e₁₂` (which satisfy `[e₁₁, e₁₂] = e₁₂`).

The problem asks to classify the irreducible finite-dimensional representations in characteristic
`0` and characteristic `p`, and whether Lie's theorem holds in characteristic `p`. We render the
book's *answers* as the statements:

* **Characteristic `0`** (algebraically closed, so Lie's theorem applies): every irreducible
  finite-dimensional representation is `1`-dimensional, and on such a representation `Y` acts as
  `0`. So the irreducibles are classified by the scalar `X ↦ λ ∈ k` (with `Y ↦ 0`).
* **Characteristic `p`**: Lie's theorem is **false** — there exist irreducible finite-dimensional
  representations of dimension `> 1` (in fact of dimension `p`).

Statement-only (proofs deferred).
-/

namespace Etingof.Problem2_16_2

open scoped Matrix

-- `LieRing.ofAssociativeRing` is a local instance from Mathlib v4.31 onward (to avoid a bracket
-- diamond when a ring acts on itself); re-enable it locally so the matrix Lie algebra elaborates.
attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type*) [Field k]

/-- The two-dimensional Lie algebra `𝔤 = ⟨X, Y | [X, Y] = Y⟩`, realized as the Lie subalgebra of
`𝔤𝔩(2, k)` spanned by the matrix units `X = e₁₁` and `Y = e₁₂`. (Etingof Problem 2.16.2) -/
noncomputable def g : LieSubalgebra k (Matrix (Fin 2) (Fin 2) k) :=
  LieSubalgebra.lieSpan k _ {Matrix.single 0 0 1, Matrix.single 0 1 1}

/-- The generator `X = e₁₁` of `𝔤`. -/
noncomputable def X : g k :=
  ⟨Matrix.single 0 0 1, LieSubalgebra.subset_lieSpan (by left; rfl)⟩

/-- The generator `Y = e₁₂` of `𝔤`. -/
noncomputable def Y : g k :=
  ⟨Matrix.single 0 1 1, LieSubalgebra.subset_lieSpan (by right; rfl)⟩

/-- The defining commutation relation `[X, Y] = Y` of `𝔤`. -/
theorem bracket_X_Y : ⁅X k, Y k⁆ = Y k :=
  sorry

/-- **Characteristic `0`.** Every irreducible finite-dimensional representation of `𝔤` is
`1`-dimensional (Lie's theorem, `k` algebraically closed of characteristic `0`). -/
theorem charZero_irreducible_finrank_one [IsAlgClosed k] [CharZero k]
    (M : Type*) [AddCommGroup M] [Module k M] [LieRingModule (g k) M] [LieModule k (g k) M]
    [FiniteDimensional k M] [LieModule.IsIrreducible k (g k) M] :
    Module.finrank k M = 1 :=
  sorry

/-- **Characteristic `0`.** On an irreducible (hence `1`-dimensional) representation, the generator
`Y` acts as `0`; thus the irreducibles are classified by the scalar `λ` with which `X` acts. -/
theorem charZero_Y_acts_zero [IsAlgClosed k] [CharZero k]
    (M : Type*) [AddCommGroup M] [Module k M] [LieRingModule (g k) M] [LieModule k (g k) M]
    [FiniteDimensional k M] [LieModule.IsIrreducible k (g k) M] (m : M) :
    ⁅Y k, m⁆ = 0 :=
  sorry

/-- **Characteristic `p`.** Lie's theorem fails: it is **not** the case that every irreducible
finite-dimensional representation of `𝔤` is `1`-dimensional. -/
theorem lie_theorem_fails_charP [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] :
    ¬ ∀ (M : Type) [AddCommGroup M] [Module k M] [LieRingModule (g k) M]
        [LieModule k (g k) M] [FiniteDimensional k M] [LieModule.IsIrreducible k (g k) M],
        Module.finrank k M = 1 :=
  sorry

end Etingof.Problem2_16_2
