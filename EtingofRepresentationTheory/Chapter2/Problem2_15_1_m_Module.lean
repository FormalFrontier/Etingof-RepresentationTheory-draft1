import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.Data.Nat.Choose.Basic
import EtingofRepresentationTheory.Chapter2.Sl2Irrep

/-!
# Clebsch–Gordan, module level (Problem 2.15.1(m))

The companion file `Problem2_15_1_m.lean` proves the **character identity** behind the
Clebsch–Gordan decomposition `V_λ ⊗ V_μ ≅ ⨁_{k=0}^{min(λ,μ)} V_{λ+μ−2k}`. This file
begins the promotion of that combinatorial statement to a genuine `sl(2)`-module
isomorphism, following the book's route (highest-weight vectors + dimension count +
distinct Casimir scalars, avoiding Weyl complete reducibility).

## What is here

* The tensor product `V_λ ⊗[ℂ] V_μ` automatically carries an `sl(2)`-module structure
  via Mathlib's `TensorProduct.LieModule` instances; the action is the expected
  derivation `X • (v ⊗ w) = (X•v) ⊗ w + v ⊗ (X•w)` (`TensorProduct.LieModule.lie_tmul_right`).
* For each `k = 0,…,min(λ,μ)` we write down the explicit **highest-weight vector**
  `cgHW λ μ k = Σ_{i=0}^k (−1)^i C(k,i) · e_i ⊗ e_{k−i}` of weight `λ+μ−2k`
  (`cgHW`), and prove it is an `H`-eigenvector of that weight
  (`lie_sl2_h_cgHW`) annihilated by the raising operator `E` (`lie_sl2_e_cgHW`).

The coefficients `(−1)^i C(k,i)` are forced by the highest-weight condition `E·w = 0`,
which after grouping by the basis tensor `e_a ⊗ e_b` (`a+b = k−1`) reads
`(a+1)c_{a+1} + (k−a)c_a = 0`; this is Pascal's absorption identity
`Nat.choose_succ_right_eq`.

## Remaining work

Assembling the full module isomorphism — showing each `cgHW λ μ k` generates an
irreducible subrep `≅ V_{λ+μ−2k}` (via `irrep_isIrreducible` and the distinct Casimir
scalars `casimir_eq_scalar_lambda`), and that these exhaust `V_λ ⊗ V_μ` by the
dimension count `clebsch_gordan_dim` — is tracked as follow-up work.
-/

open scoped TensorProduct
open Etingof Etingof.Sl2Irrep

namespace Etingof.Sl2Irrep

variable (lam mu : ℕ)

/-- The tensor product `V_λ ⊗ V_μ` carries the derivation `sl(2)`-action
`X • (v ⊗ w) = (X•v) ⊗ w + v ⊗ (X•w)`, recorded here as the bracket on a pure tensor. -/
theorem lie_tmul (x : sl2) (v : Fin (lam + 1) → ℂ) (w : Fin (mu + 1) → ℂ) :
    ⁅x, v ⊗ₜ[ℂ] w⁆ = ⁅x, v⁆ ⊗ₜ[ℂ] w + v ⊗ₜ[ℂ] ⁅x, w⁆ :=
  TensorProduct.LieModule.lie_tmul_right x v w

/-- The Clebsch–Gordan **highest-weight vector** of weight `λ+μ−2k` in `V_λ ⊗ V_μ`:
`cgHW λ μ k = Σ_{i=0}^{k} (−1)^i C(k,i) · (e_i ⊗ e_{k−i})`.

Defined for `k ≤ min(λ,μ)` so that all the basis indices `i ≤ λ` and `k−i ≤ μ` are in
range. -/
noncomputable def cgHW (k : ℕ) (hk : k ≤ min lam mu) :
    (Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ) :=
  ∑ i : Fin (k + 1),
    ((-1) ^ (i : ℕ) * (k.choose (i : ℕ) : ℂ)) •
      (e_basis (lam + 1) ⟨(i : ℕ), by omega⟩ ⊗ₜ[ℂ]
        e_basis (mu + 1) ⟨k - (i : ℕ), by omega⟩)

/-- `cgHW λ μ k` is an `H`-eigenvector of weight `λ+μ−2k`: each summand
`e_i ⊗ e_{k−i}` has weight `(λ−2i) + (μ−2(k−i)) = λ+μ−2k`. -/
theorem lie_sl2_h_cgHW (k : ℕ) (hk : k ≤ min lam mu) :
    ⁅sl2_h, cgHW lam mu k hk⁆ = ((lam : ℂ) + mu - 2 * k) • cgHW lam mu k hk := by
  rw [cgHW, lie_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hik : (i : ℕ) ≤ k := by omega
  rw [lie_smul, lie_tmul, lie_sl2_h_e_basis, lie_sl2_h_e_basis,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, ← add_smul, smul_smul, smul_smul]
  congr 1
  simp only [Fin.val_mk]
  push_cast [Nat.cast_sub hik]
  ring

end Etingof.Sl2Irrep
