import Mathlib
import EtingofRepresentationTheory.Chapter2.Problem2_16_2

/-!
# Concrete Lie algebra examples (continued): `aff(1)`

The book's continued list of concrete Lie algebras names

`aff(1) = { [[a, b], [0, 0]] }`,

the Lie algebra of `2 × 2` matrices whose bottom row vanishes, with basis
`X = E₀₀`, `Y = E₀₁` and commutation relation `[X, Y] = Y`.

The core algebra is already present in `Problem2_16_2`: the public `Etingof.Problem2_16_2.g k`
is the Lie subalgebra of `𝔤𝔩(2, k)` spanned by the matrix units `X = E₀₀` and `Y = E₀₁`,
`X` and `Y` are those matrices, and `bracket_X_Y` proves `[X, Y] = Y`. Here we identify that
construction as the book's `aff(1)`: we expose the source-facing alias `aff k`, prove that
`X, Y` form a basis of `aff(1)` (so it is two-dimensional), and identify `aff(1)` with the Lie
subalgebra `rowZero` of all `2 × 2` matrices whose bottom row is zero.

The `𝔰𝔬(n)` half of the continued list is supplied by Mathlib's `LieAlgebra.Orthogonal.so`.
-/

namespace Etingof.Problem2_16_2

open scoped Matrix
open Module

-- `LieRing.ofAssociativeRing` is a local instance in Mathlib; re-enable it so the matrix Lie
-- algebra `g k = aff(1)` and its bracket elaborate (as in `Problem2_16_2`).
attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type) [Field k]

/-- The Lie algebra `aff(1)` of `2 × 2` matrices `[[a, b], [0, 0]]` with vanishing bottom row,
realized as the Lie subalgebra of `𝔤𝔩(2, k)` spanned by the matrix units `X = E₀₀` and
`Y = E₀₁`. This is exactly `Problem2_16_2.g`, whose defining relation is `[X, Y] = Y`
(`bracket_X_Y`). -/
noncomputable abbrev aff : LieSubalgebra k (Matrix (Fin 2) (Fin 2) k) := g k

/-- Every element of `aff(1)` is recovered from its two top-row entries: it is the combination
`(z 0 0) • X + (z 0 1) • Y` of the two generators. This is the coordinate description underlying
the basis `X, Y`. -/
theorem coe_eq_smul_add (z : g k) :
    (z : Matrix (Fin 2) (Fin 2) k)
      = (z : Matrix (Fin 2) (Fin 2) k) 0 0 • Matrix.single 0 0 1
        + (z : Matrix (Fin 2) (Fin 2) k) 0 1 • Matrix.single 0 1 1 := by
  obtain ⟨h10, h11⟩ := mem_g_row k z
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply, h10, h11]

/-- `X` and `Y` are linearly independent in `aff(1)`. -/
theorem linearIndependent_XY : LinearIndependent k ![X k, Y k] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  -- transport the vanishing combination to the ambient matrix algebra
  have hcoe : c 0 • Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : k)
      + c 1 • Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : k) = 0 := by
    have h2 : ((∑ j, c j • (![X k, Y k] j) : g k) : Matrix (Fin 2) (Fin 2) k)
        = ((0 : g k) : Matrix (Fin 2) (Fin 2) k) := congrArg _ hc
    rw [Fin.sum_univ_two] at h2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h2
    push_cast at h2
    rw [coe_X, coe_Y] at h2
    simpa using h2
  fin_cases i
  · have h00 := congrFun (congrFun hcoe 0) 0
    simpa [Matrix.single_apply, Matrix.add_apply, Matrix.smul_apply] using h00
  · have h01 := congrFun (congrFun hcoe 0) 1
    simpa [Matrix.single_apply, Matrix.add_apply, Matrix.smul_apply] using h01

/-- `X` and `Y` span `aff(1)`. -/
theorem span_XY : Submodule.span k (Set.range ![X k, Y k]) = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  have hz : z = (z : Matrix (Fin 2) (Fin 2) k) 0 0 • X k
      + (z : Matrix (Fin 2) (Fin 2) k) 0 1 • Y k := by
    apply Subtype.ext
    push_cast
    rw [coe_X, coe_Y]
    exact coe_eq_smul_add k z
  rw [hz]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
  · exact Submodule.subset_span ⟨0, rfl⟩
  · exact Submodule.subset_span ⟨1, rfl⟩

/-- The basis `X = E₀₀`, `Y = E₀₁` of `aff(1)`. -/
noncomputable def basisXY : Basis (Fin 2) k (g k) :=
  Basis.mk (linearIndependent_XY k) (le_of_eq (span_XY k).symm)

@[simp] theorem basisXY_apply (i : Fin 2) : basisXY k i = ![X k, Y k] i :=
  Basis.mk_apply _ _ i

/-- `aff(1)` is two-dimensional. -/
theorem finrank_aff : Module.finrank k (g k) = 2 := by
  rw [Module.finrank_eq_card_basis (basisXY k), Fintype.card_fin]

/-- `aff(1)` is exactly the Lie subalgebra of all `2 × 2` matrices whose bottom row vanishes. -/
theorem g_eq_rowZero : g k = rowZero k := by
  refine le_antisymm ?_ ?_
  · intro z hz
    exact mem_g_row k ⟨z, hz⟩
  · intro A hA
    obtain ⟨h10, h11⟩ := hA
    -- `A = (A 0 0) • E₀₀ + (A 0 1) • E₀₁`, and both generators lie in `g k`.
    have hA_eq : A = A 0 0 • Matrix.single 0 0 1 + A 0 1 • Matrix.single 0 1 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply, h10, h11]
    rw [hA_eq]
    refine (g k).toSubmodule.add_mem
      ((g k).toSubmodule.smul_mem _ ?_) ((g k).toSubmodule.smul_mem _ ?_)
    · exact LieSubalgebra.subset_lieSpan (by left; rfl)
    · exact LieSubalgebra.subset_lieSpan (by right; rfl)

end Etingof.Problem2_16_2
