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

/-- The `e_{i-1} ⊗ e_{k-i}` summand of `⁅E, cgHW⁆` (the raising operator acting on the
first tensor factor). -/
private noncomputable def cgA (k : ℕ) (hk : k ≤ min lam mu) (i : Fin (k + 1)) :
    (Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ) :=
  (((-1) ^ (i : ℕ) * (k.choose (i : ℕ) : ℂ)) * (i : ℕ)) •
    (e_basis (lam + 1) ⟨(i : ℕ) - 1, by omega⟩ ⊗ₜ[ℂ]
      e_basis (mu + 1) ⟨k - (i : ℕ), by omega⟩)

/-- The `e_i ⊗ e_{k-i-1}` summand of `⁅E, cgHW⁆` (the raising operator acting on the
second tensor factor). -/
private noncomputable def cgB (k : ℕ) (hk : k ≤ min lam mu) (i : Fin (k + 1)) :
    (Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ) :=
  (((-1) ^ (i : ℕ) * (k.choose (i : ℕ) : ℂ)) * ((k - (i : ℕ) : ℕ) : ℂ)) •
    (e_basis (lam + 1) ⟨(i : ℕ), by omega⟩ ⊗ₜ[ℂ]
      e_basis (mu + 1) ⟨k - (i : ℕ) - 1, by omega⟩)

/-- `cgHW λ μ k` is annihilated by the raising operator `E`: it is a highest-weight
vector. After grouping `⁅E, ·⁆` by basis tensor, the coefficient of `e_i ⊗ e_{k-1-i}`
is `(i+1)c_{i+1} + (k-i)c_i = 0`, which is Pascal's absorption identity. -/
theorem lie_sl2_e_cgHW (k : ℕ) (hk : k ≤ min lam mu) :
    ⁅sl2_e, cgHW lam mu k hk⁆ = 0 := by
  rw [cgHW, lie_sum]
  have hterm : ∀ i : Fin (k + 1),
      ⁅sl2_e, ((-1) ^ (i : ℕ) * (k.choose (i : ℕ) : ℂ)) •
        (e_basis (lam + 1) ⟨(i : ℕ), by omega⟩ ⊗ₜ[ℂ]
          e_basis (mu + 1) ⟨k - (i : ℕ), by omega⟩)⁆
        = cgA lam mu k hk i + cgB lam mu k hk i := by
    intro i
    rw [lie_smul, lie_tmul,
      lie_sl2_e_e_basis (lam + 1) (i : ℕ) (by omega),
      lie_sl2_e_e_basis (mu + 1) (k - (i : ℕ)) (by omega),
      ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add, smul_smul, smul_smul]
    rfl
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib]
  conv_lhs =>
    rw [Fin.sum_univ_succ (cgA lam mu k hk), Fin.sum_univ_castSucc (cgB lam mu k hk)]
  rw [show cgA lam mu k hk 0 = 0 by simp [cgA],
    show cgB lam mu k hk (Fin.last k) = 0 by simp [cgB, Fin.val_last],
    zero_add, add_zero, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  have hik : (i : ℕ) ≤ k := by omega
  have key : (k.choose ((i : ℕ) + 1) : ℂ) * (((i : ℕ) + 1 : ℕ) : ℂ)
      = (k.choose (i : ℕ) : ℂ) * ((k - (i : ℕ) : ℕ) : ℂ) := by
    exact_mod_cast Nat.choose_succ_right_eq k (i : ℕ)
  simp only [cgA, cgB, Fin.val_succ, Fin.coe_castSucc,
    Nat.add_sub_cancel, Nat.sub_sub]
  rw [← add_smul]
  convert zero_smul ℂ _ using 2
  rw [pow_succ]
  linear_combination (-(-1 : ℂ) ^ (i : ℕ)) * key

/-- The Clebsch–Gordan highest-weight vector `cgHW λ μ k` is nonzero: its
`e_0 ⊗ e_k` coefficient is `(−1)^0 C(k,0) = 1`. We read it off with the linear
functional `v ⊗ w ↦ v 0 · w k`, which sends `cgHW λ μ k` to `1`. -/
theorem cgHW_ne_zero (k : ℕ) (hk : k ≤ min lam mu) : cgHW lam mu k hk ≠ 0 := by
  have hkmu : k < mu + 1 := by omega
  -- functional extracting the coefficient of `e_0 ⊗ e_k`
  set φ : (Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ) →ₗ[ℂ] ℂ :=
    TensorProduct.lift
      ((LinearMap.mul ℂ ℂ).compl₁₂ (LinearMap.proj (0 : Fin (lam + 1)))
        (LinearMap.proj (⟨k, hkmu⟩ : Fin (mu + 1)))) with hφ
  have hval : φ (cgHW lam mu k hk) = 1 := by
    rw [cgHW, map_sum]
    rw [Finset.sum_eq_single (0 : Fin (k + 1))]
    · simp [hφ, e_basis_apply]
    · intro i _ hi
      have hi' : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
      simp only [hφ, map_smul, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply,
        LinearMap.proj_apply, LinearMap.mul_apply', e_basis_apply]
      rw [if_neg (by rw [Fin.ext_iff]; simpa using hi'.symm)]
      ring
    · intro h; exact absurd (Finset.mem_univ _) h
  intro h0
  rw [h0, map_zero] at hval
  exact zero_ne_one hval

/-! ## The Casimir scalar on the highest-weight vectors

The Casimir operator `C = EF + FE + H²/2` acts on a highest-weight vector `w` of
weight `ν` by the scalar `ν(ν+2)/2`: since `E·w = 0`,
`EF·w = ⁅E, F·w⁆ = ⁅⁅E,F⁆, w⁆ + ⁅F, E·w⁆ = H·w = ν·w` (Jacobi, `⁅E,F⁆ = H`),
`FE·w = 0`, and `H²·w = ν²·w`, so `C·w = (ν + ν²/2)·w = (ν(ν+2)/2)·w`.

On `cgHW λ μ k` the weight is `ν = λ+μ−2k`, giving the value
`(λ+μ−2k)(λ+μ−2k+2)/2`. These scalars are pairwise distinct for
`k = 0,…,min(λ,μ)` (the map `ν ↦ ν(ν+2)/2` is injective on `ν ≥ 0`), so the
Casimir operator separates the Clebsch–Gordan summands — the tool used in the
assembly of the full module isomorphism. -/

/-- **Casimir scalar on the Clebsch–Gordan highest-weight vector.** The Casimir
operator `C = EF + FE + H²/2` of `sl(2)` acts on `cgHW λ μ k` (a highest-weight
vector of weight `ν = λ+μ−2k`) as the scalar `ν(ν+2)/2`. The distinct values of
this scalar for different `k` separate the irreducible summands of `V_λ ⊗ V_μ`. -/
theorem casimir_cgHW (k : ℕ) (hk : k ≤ min lam mu) :
    ⁅sl2_e, ⁅sl2_f, cgHW lam mu k hk⁆⁆
        + ⁅sl2_f, ⁅sl2_e, cgHW lam mu k hk⁆⁆
        + (2⁻¹ : ℂ) • ⁅sl2_h, ⁅sl2_h, cgHW lam mu k hk⁆⁆
      = ((((lam : ℂ) + mu - 2 * k) * ((lam : ℂ) + mu - 2 * k + 2)) / 2)
          • cgHW lam mu k hk := by
  have hE : ⁅sl2_e, cgHW lam mu k hk⁆ = 0 := lie_sl2_e_cgHW lam mu k hk
  have hH : ⁅sl2_h, cgHW lam mu k hk⁆
      = ((lam : ℂ) + mu - 2 * k) • cgHW lam mu k hk := lie_sl2_h_cgHW lam mu k hk
  -- `EF·w = ⁅⁅E,F⁆, w⁆ + ⁅F, E·w⁆ = H·w = ν·w` (Jacobi and `⁅E,F⁆ = H`).
  have hEF : ⁅sl2_e, ⁅sl2_f, cgHW lam mu k hk⁆⁆
      = ((lam : ℂ) + mu - 2 * k) • cgHW lam mu k hk := by
    rw [leibniz_lie sl2_e sl2_f, lie_e_f, hH, hE, lie_zero, add_zero]
  -- `FE·w = 0` since `E·w = 0`.
  have hFE : ⁅sl2_f, ⁅sl2_e, cgHW lam mu k hk⁆⁆ = 0 := by rw [hE, lie_zero]
  -- `H²·w = ν²·w`.
  have hHH : ⁅sl2_h, ⁅sl2_h, cgHW lam mu k hk⁆⁆
      = (((lam : ℂ) + mu - 2 * k) * ((lam : ℂ) + mu - 2 * k)) • cgHW lam mu k hk := by
    rw [hH, lie_smul, hH, smul_smul]
  rw [hEF, hFE, hHH, add_zero, smul_smul, ← add_smul]
  congr 1
  ring

end Etingof.Sl2Irrep
