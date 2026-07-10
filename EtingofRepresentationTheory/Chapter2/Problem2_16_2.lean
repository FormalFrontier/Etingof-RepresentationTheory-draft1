import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.Lie.Submodule
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Module.Equiv.Basic

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

/-! ## Characteristic `p`: an irreducible representation of dimension `p`

We realize the book's counterexample to Lie's theorem in characteristic `p`. Let `M = k^{ℤ/p}`
(functions on `ℤ/p`). We let `X` act by the diagonal operator `diagOp` with the `p` distinct
eigenvalues `0, 1, …, p-1` (the image of `ℤ/p` in `k` under the prime-field embedding) and `Y`
act by the cyclic shift `shiftOp`. These satisfy `[diagOp, shiftOp] = shiftOp`, matching
`[X, Y] = Y`, so they assemble into a representation `ρ : 𝔤 → End k M`. The resulting module is
irreducible of dimension `p > 1`, so Lie's theorem fails.

Because the counterexample module `k^{ℤ/p}` lives in the same universe as `k`, and the theorem
`lie_theorem_fails_charP` quantifies over `M : Type` (universe `0`), we specialize `k` to
`Type` here (the char-`0` results above keep `k : Type*`). -/

section CharP

variable (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The prime-field embedding `ℤ/p ↪ k`, whose values `0, 1, …, p-1` are the `p` distinct
eigenvalues of the diagonal operator. -/
noncomputable def lam : ZMod p →+* k := ZMod.castHom (dvd_refl p) k

theorem lam_injective : Function.Injective (lam k p) := by
  show Function.Injective ⇑(ZMod.castHom (dvd_refl p) k)
  exact ZMod.castHom_injective k

/-- The diagonal operator on `k^{ℤ/p}`: `(diagOp v) i = (i : k) * v i`, with distinct
eigenvalues indexed by `ℤ/p`. This is the action of `X`. -/
noncomputable def diagOp : Module.End k (ZMod p → k) where
  toFun v i := lam k p i * v i
  map_add' u v := by funext i; simp only [Pi.add_apply]; ring
  map_smul' c v := by funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The cyclic shift on `k^{ℤ/p}`: `(shiftOp v) i = v (i - 1)`. This is the action of `Y`. -/
noncomputable def shiftOp : Module.End k (ZMod p → k) :=
  LinearMap.funLeft k k (fun i => i - 1)

variable {k p}

@[simp] theorem diagOp_apply (v : ZMod p → k) (i : ZMod p) : diagOp k p v i = lam k p i * v i :=
  rfl

@[simp] theorem shiftOp_apply (v : ZMod p → k) (i : ZMod p) : shiftOp k p v i = v (i - 1) :=
  rfl

/-- The key relation `[diagOp, shiftOp] = shiftOp`, mirroring `[X, Y] = Y`. It holds because the
prime-field embedding is a ring homomorphism, so consecutive eigenvalues differ by `lam 1 = 1`. -/
theorem bracket_diag_shift : ⁅diagOp k p, shiftOp k p⁆ = shiftOp k p := by
  refine LinearMap.ext fun v => funext fun i => ?_
  simp only [Ring.lie_def, LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply,
    diagOp_apply, shiftOp_apply]
  rw [← sub_mul, ← map_sub, sub_sub_cancel, map_one, one_mul]

variable (k p)

/-- Auxiliary Lie subalgebra of `2×2` matrices whose second row vanishes. It contains the
generators `e₁₁, e₁₂`, hence contains all of `g k`; this pins down the entries of elements of
`g k` used in the bracket computation for `ρ`. -/
def rowZero : LieSubalgebra k (Matrix (Fin 2) (Fin 2) k) where
  carrier := {A | A 1 0 = 0 ∧ A 1 1 = 0}
  add_mem' {a b} ha hb := ⟨by simp [ha.1, hb.1], by simp [ha.2, hb.2]⟩
  zero_mem' := ⟨rfl, rfl⟩
  smul_mem' c a ha := ⟨by simp [ha.1], by simp [ha.2]⟩
  lie_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply,
      Fin.sum_univ_two, ha.1, ha.2, hb.1, hb.2, zero_mul, mul_zero, add_zero, sub_zero, and_self]

/-- Every element of `g k` has vanishing second row. -/
theorem mem_g_row (A : g k) :
    (↑A : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 ∧ (↑A : Matrix (Fin 2) (Fin 2) k) 1 1 = 0 := by
  have hg : g k = LieSubalgebra.lieSpan k (Matrix (Fin 2) (Fin 2) k)
      {Matrix.single 0 0 1, Matrix.single 0 1 1} := rfl
  have hle : g k ≤ rowZero k := by
    rw [hg, LieSubalgebra.lieSpan_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨by simp [Matrix.single_apply], by simp [Matrix.single_apply]⟩
    · exact ⟨by simp [Matrix.single_apply], by simp [Matrix.single_apply]⟩
  exact hle A.2

/-- The representation `ρ : 𝔤 → End k M` sending `X ↦ diagOp`, `Y ↦ shiftOp`, defined on a
matrix `A ∈ 𝔤` by `A ↦ A₀₀ • diagOp + A₀₁ • shiftOp`. -/
noncomputable def ρ : g k →ₗ⁅k⁆ Module.End k (ZMod p → k) where
  toFun A := (A : Matrix (Fin 2) (Fin 2) k) 0 0 • diagOp k p
    + (A : Matrix (Fin 2) (Fin 2) k) 0 1 • shiftOp k p
  map_add' A B := by
    simp only [AddMemClass.coe_add, Matrix.add_apply, add_smul]; abel
  map_smul' c A := by
    simp only [SetLike.val_smul, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add,
      smul_smul]
  map_lie' := by
    intro A B
    -- The second row of any element of `g k` vanishes; use it to compute the two relevant
    -- entries of the matrix commutator `⁅A, B⁆`.
    obtain ⟨hA0, hA1⟩ := mem_g_row k A
    obtain ⟨hB0, hB1⟩ := mem_g_row k B
    have hds : ⁅shiftOp k p, diagOp k p⁆ = -shiftOp k p := by
      rw [← lie_skew, bracket_diag_shift]
    have hbr : (↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k)
        = (↑A : Matrix (Fin 2) (Fin 2) k) * (↑B : Matrix (Fin 2) (Fin 2) k)
          - (↑B : Matrix (Fin 2) (Fin 2) k) * (↑A : Matrix (Fin 2) (Fin 2) k) := by
      rw [LieSubalgebra.coe_bracket, Ring.lie_def]
    have e00 : (↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k) 0 0 = 0 := by
      rw [hbr]
      simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, hA0, hB0, mul_zero,
        add_zero]
      ring
    have e01 : (↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k) 0 1 =
        (↑A : Matrix (Fin 2) (Fin 2) k) 0 0 * (↑B : Matrix (Fin 2) (Fin 2) k) 0 1
          - (↑B : Matrix (Fin 2) (Fin 2) k) 0 0 * (↑A : Matrix (Fin 2) (Fin 2) k) 0 1 := by
      rw [hbr]
      simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, hA1, hB1, mul_zero,
        add_zero]
    show (↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k) 0 0 • diagOp k p
        + (↑⁅A, B⁆ : Matrix (Fin 2) (Fin 2) k) 0 1 • shiftOp k p
      = ⁅(↑A : Matrix (Fin 2) (Fin 2) k) 0 0 • diagOp k p
          + (↑A : Matrix (Fin 2) (Fin 2) k) 0 1 • shiftOp k p,
        (↑B : Matrix (Fin 2) (Fin 2) k) 0 0 • diagOp k p
          + (↑B : Matrix (Fin 2) (Fin 2) k) 0 1 • shiftOp k p⁆
    rw [e00, e01]
    simp only [add_lie, lie_add, smul_lie, lie_smul, lie_self, smul_zero, add_zero, zero_add,
      bracket_diag_shift, hds, smul_neg, zero_smul]
    module

/-- Coercion of the generator `X = e₁₁` to the underlying matrix. -/
theorem coe_X : (↑(X k) : Matrix (Fin 2) (Fin 2) k) = Matrix.single 0 0 1 := rfl

/-- Coercion of the generator `Y = e₁₂` to the underlying matrix. -/
theorem coe_Y : (↑(Y k) : Matrix (Fin 2) (Fin 2) k) = Matrix.single 0 1 1 := rfl

/-- Under `ρ`, the generator `X` acts as the diagonal operator. -/
@[simp] theorem ρ_X : ρ k p (X k) = diagOp k p := by
  have h0 : (Matrix.single 0 0 (1 : k) : Matrix (Fin 2) (Fin 2) k) 0 0 = 1 := by
    simp [Matrix.single_apply]
  have h1 : (Matrix.single 0 0 (1 : k) : Matrix (Fin 2) (Fin 2) k) 0 1 = 0 := by
    simp [Matrix.single_apply]
  show (↑(X k) : Matrix (Fin 2) (Fin 2) k) 0 0 • diagOp k p
      + (↑(X k) : Matrix (Fin 2) (Fin 2) k) 0 1 • shiftOp k p = diagOp k p
  rw [coe_X, h0, h1, one_smul, zero_smul, add_zero]

/-- Under `ρ`, the generator `Y` acts as the cyclic shift. -/
@[simp] theorem ρ_Y : ρ k p (Y k) = shiftOp k p := by
  have h0 : (Matrix.single 0 1 (1 : k) : Matrix (Fin 2) (Fin 2) k) 0 0 = 0 := by
    simp [Matrix.single_apply]
  have h1 : (Matrix.single 0 1 (1 : k) : Matrix (Fin 2) (Fin 2) k) 0 1 = 1 := by
    simp [Matrix.single_apply]
  show (↑(Y k) : Matrix (Fin 2) (Fin 2) k) 0 0 • diagOp k p
      + (↑(Y k) : Matrix (Fin 2) (Fin 2) k) 0 1 • shiftOp k p = shiftOp k p
  rw [coe_Y, h0, h1, zero_smul, one_smul, zero_add]

/-- **Characteristic `p`.** Lie's theorem fails: it is **not** the case that every irreducible
finite-dimensional representation of `𝔤` is `1`-dimensional. -/
theorem lie_theorem_fails_charP (k : Type) [Field k] [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] [CharP k p] :
    ¬ ∀ (M : Type) [AddCommGroup M] [Module k M] [LieRingModule (g k) M]
        [LieModule k (g k) M] [FiniteDimensional k M] [LieModule.IsIrreducible k (g k) M],
        Module.finrank k M = 1 :=
  sorry

end CharP

end Etingof.Problem2_16_2
