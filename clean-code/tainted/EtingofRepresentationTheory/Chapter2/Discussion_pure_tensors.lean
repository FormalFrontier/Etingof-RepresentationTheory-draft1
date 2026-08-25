import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Discussion (pure tensors): not every tensor is pure

The prose following Definition 2.4 introduces the **pure tensors** `v ⊗ w ∈ V ⊗ W` and remarks
that, in general, `V ⊗ W` contains elements which are *not* pure tensors.

Mathlib's `TensorProduct.span_tmul_eq_top` records that pure tensors *span* the tensor product,
but it says nothing about whether an individual element is pure, and it supplies no
counterexample. This file provides the missing explicit witness.

Working over `ℚ` with `V = W = Fin 2 → ℚ` and standard basis vectors `e 0, e 1`, the tensor

`t = e 0 ⊗ₜ e 0 + e 1 ⊗ₜ e 1`

is not pure: `t ≠ v ⊗ₜ w` for every `v, w`. Conceptually `t` corresponds to the `2 × 2`
identity matrix, which has rank `2`, while a pure tensor `v ⊗ w` corresponds to the rank `≤ 1`
outer product `(v i · w j)`. We make this elementary by extracting the four coordinate entries
`c i j` of a tensor and deriving a direct numerical contradiction.

The continuation of the discussion defines tensors of type `(m,n)` and displays their basis in
terms of a finite basis of `V` and its dual basis. The declarations `TensorTypes.TensorType` and
`TensorTypes.tensorTypeBasis` record that definition and basis directly.
-/

open scoped TensorProduct

namespace Etingof

namespace PureTensors

/-- The ambient space: two-dimensional coordinate space over `ℚ`. -/
abbrev V : Type := Fin 2 → ℚ

/-- The standard basis vectors `e 0, e 1` of `V`. -/
noncomputable def e (i : Fin 2) : V := Pi.single i 1

/-- The `(i, j)` coordinate functional on `V ⊗ V`, sending a pure tensor `v ⊗ w` to `v i * w j`.
Under the identification of `V ⊗ V` with `2 × 2` matrices this reads off the `(i, j)` entry. -/
noncomputable def coeff (i j : Fin 2) : (V ⊗[ℚ] V) →ₗ[ℚ] ℚ :=
  TensorProduct.lift (((LinearMap.mul ℚ ℚ).comp (LinearMap.proj i)).compl₂ (LinearMap.proj j))

/-- Evaluating the coordinate functional on a pure tensor gives the product of coordinates. -/
@[simp]
lemma coeff_tmul (i j : Fin 2) (v w : V) : coeff i j (v ⊗ₜ[ℚ] w) = v i * w j := by
  simp [coeff]

/-- The candidate non-pure tensor `t = e 0 ⊗ e 0 + e 1 ⊗ e 1`. -/
noncomputable def t : V ⊗[ℚ] V := e 0 ⊗ₜ[ℚ] e 0 + e 1 ⊗ₜ[ℚ] e 1

/-- The coordinate entries of `t` form the identity pattern: `c i j t = 1` if `i = j`, else `0`. -/
lemma coeff_t (i j : Fin 2) : coeff i j t = if i = j then 1 else 0 := by
  simp only [t, map_add, coeff_tmul, e, Pi.single_apply]
  fin_cases i <;> fin_cases j <;> norm_num

/-- **Not every tensor is pure.** The tensor `t = e 0 ⊗ e 0 + e 1 ⊗ e 1` in
`(Fin 2 → ℚ) ⊗ (Fin 2 → ℚ)` is not a pure tensor: there is no pair `v, w` with `t = v ⊗ₜ w`. -/
theorem t_not_pure (v w : V) : t ≠ v ⊗ₜ[ℚ] w := by
  intro h
  -- Apply the four coordinate functionals to both sides of `h`.
  have h00 : v 0 * w 0 = 1 := by
    have := congrArg (coeff 0 0) h
    rw [coeff_t, coeff_tmul, if_pos rfl] at this
    exact this.symm
  have h01 : v 0 * w 1 = 0 := by
    have := congrArg (coeff 0 1) h
    rw [coeff_t, coeff_tmul, if_neg (by decide)] at this
    exact this.symm
  have h11 : v 1 * w 1 = 1 := by
    have := congrArg (coeff 1 1) h
    rw [coeff_t, coeff_tmul, if_pos rfl] at this
    exact this.symm
  -- `v 0 ≠ 0` from `h00`, so `w 1 = 0` from `h01`, contradicting `h11`.
  have hv0 : v 0 ≠ 0 := by
    intro hv
    rw [hv, zero_mul] at h00
    exact one_ne_zero h00.symm
  have hw1 : w 1 = 0 := by
    rcases mul_eq_zero.mp h01 with hv | hw
    · exact absurd hv hv0
    · exact hw
  rw [hw1, mul_zero] at h11
  exact one_ne_zero h11.symm

end PureTensors

namespace TensorTypes

open scoped TensorProduct

/-- The book's space of tensors of type `(m,n)` on `V`:
`V^{⊗ n} ⊗ (V*)^{⊗ m}`. -/
abbrev TensorType (k V : Type*) [CommRing k] [AddCommGroup V] [Module k V]
    (m n : ℕ) : Type _ :=
  (⨂[k] (_ : Fin n), V) ⊗[k] (⨂[k] (_ : Fin m), Module.Dual k V)

/-- If `b = (eᵢ)` is a finite basis of `V`, the tensors
`e_{i₁} ⊗ ⋯ ⊗ e_{iₙ} ⊗ e^{j₁} ⊗ ⋯ ⊗ e^{jₘ}` form a basis of the tensors of type `(m,n)`. -/
noncomputable def tensorTypeBasis {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V]
    [Finite ι] (b : Module.Basis ι k V) (m n : ℕ) :
    Module.Basis ((Fin n → ι) × (Fin m → ι)) k (TensorType k V m n) := by
  classical
  exact (Basis.piTensorProduct (fun _ : Fin n => b)).tensorProduct
    (Basis.piTensorProduct (fun _ : Fin m => b.dualBasis))

end TensorTypes

end Etingof
