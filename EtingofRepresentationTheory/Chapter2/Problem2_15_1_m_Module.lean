import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import EtingofRepresentationTheory.Chapter2.Sl2Irrep
import EtingofRepresentationTheory.Chapter2.Problem2_15_1_m
import EtingofRepresentationTheory.Chapter2.Problem2_15_1_complete_reducibility

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

/-! ## The highest-weight ladder in an arbitrary `sl(2)`-module

These are the general `sl(2)`-representation-theory identities for a highest-weight vector
`w` (annihilated by `E`, eigenvector of `H` of weight `ν`): applying the lowering operator
`F` repeatedly produces the weight ladder. `fIter n w = F^n w` is an `H`-eigenvector of
weight `ν - 2n` (`lie_sl2_h_fIter`), and `E` sends `F^{n+1} w` back up to a scalar multiple
of `F^n w` with the standard coefficient `(n+1)(ν-n)` (`lie_sl2_e_fIter`). They are the tools
that turn each Clebsch–Gordan highest-weight vector `cgHW λ μ k` into an irreducible subrep
`≅ V_{λ+μ−2k}`. -/

section Ladder

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
  [LieRingModule sl2 M] [LieModule ℂ sl2 M]

/-- The iterated lowering operator `F^n` acting on `M`. -/
noncomputable def fIter (n : ℕ) (w : M) : M := (fun v => ⁅sl2_f, v⁆)^[n] w

omit [Module ℂ M] [LieModule ℂ sl2 M] in
@[simp] theorem fIter_zero (w : M) : fIter 0 w = w := rfl

omit [Module ℂ M] [LieModule ℂ sl2 M] in
theorem fIter_succ (n : ℕ) (w : M) : fIter (n + 1) w = ⁅sl2_f, fIter n w⁆ :=
  Function.iterate_succ_apply' _ _ _

/-- `fIter n = F^n` matches the iterated Lie endomorphism `toEnd f ^ n`, the form used
by Mathlib's `sl(2)` primitive-vector API. -/
theorem fIter_eq_toEnd_pow (n : ℕ) (w : M) :
    fIter n w = ((LieModule.toEnd ℂ sl2 M sl2_f) ^ n) w := by
  have hfun : (fun v => ⁅sl2_f, v⁆) = ⇑(LieModule.toEnd ℂ sl2 M sl2_f) := by
    funext v; rw [LieModule.toEnd_apply_apply]
  rw [fIter, Module.End.pow_apply, hfun]

/-- **Weight ladder.** If `w` is an `H`-eigenvector of weight `ν`, then `F^n w` is an
`H`-eigenvector of weight `ν - 2n`: each application of `F` lowers the weight by `2`. -/
theorem lie_sl2_h_fIter (ν : ℂ) (w : M) (hH : ⁅sl2_h, w⁆ = ν • w) (n : ℕ) :
    ⁅sl2_h, fIter n w⁆ = (ν - 2 * n) • fIter n w := by
  induction n with
  | zero => simpa using hH
  | succ n ih =>
    rw [fIter_succ, leibniz_lie sl2_h sl2_f, lie_h_f, ih]
    rw [neg_lie, nsmul_lie, lie_smul, two_nsmul]
    push_cast
    module

/-- **Raising back up the ladder.** If `w` is a highest-weight vector (killed by `E`,
`H`-eigenvector of weight `ν`), then `E (F^{n+1} w) = (n+1)(ν-n) · F^n w`. -/
theorem lie_sl2_e_fIter (ν : ℂ) (w : M) (hE : ⁅sl2_e, w⁆ = 0) (hH : ⁅sl2_h, w⁆ = ν • w)
    (n : ℕ) :
    ⁅sl2_e, fIter (n + 1) w⁆ = (((n : ℂ) + 1) * (ν - n)) • fIter n w := by
  induction n with
  | zero =>
    rw [fIter_succ, fIter_zero, leibniz_lie sl2_e sl2_f, lie_e_f, hE, lie_zero, add_zero, hH]
    push_cast; module
  | succ n ih =>
    rw [fIter_succ, leibniz_lie sl2_e sl2_f, lie_e_f,
      lie_sl2_h_fIter ν w hH (n + 1), ih, lie_smul, ← fIter_succ]
    push_cast
    module

end Ladder

/-! ## Reducing intertwining to the generators `h, e, f`

A linear map between `sl(2)`-modules is a Lie-module hom as soon as it intertwines the
three standard generators `h, e, f`: every `X ∈ sl(2)` is the combination
`X₀₀·h + X₀₁·e + X₁₀·f` (tracelessness makes `X₁₁ = −X₀₀` redundant), so the action of
`X` is a linear combination of the actions of `h, e, f`. -/

section Intertwine

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule sl2 V] [LieModule ℂ sl2 V]
  [AddCommGroup W] [Module ℂ W] [LieRingModule sl2 W] [LieModule ℂ sl2 W]

/-- A linear map between `sl(2)`-modules intertwining the standard generators `h, e, f`
intertwines the action of every `X ∈ sl(2)`. -/
theorem map_lie_of_gens (φ : V →ₗ[ℂ] W)
    (hh : ∀ v, φ ⁅sl2_h, v⁆ = ⁅sl2_h, φ v⁆)
    (he : ∀ v, φ ⁅sl2_e, v⁆ = ⁅sl2_e, φ v⁆)
    (hf : ∀ v, φ ⁅sl2_f, v⁆ = ⁅sl2_f, φ v⁆)
    (x : sl2) (v : V) : φ ⁅x, v⁆ = ⁅x, φ v⁆ := by
  conv_lhs => rw [sl2_decomp x]
  conv_rhs => rw [sl2_decomp x]
  simp only [add_lie, smul_lie, map_add, map_smul, hh, he, hf]

/-- Package a linear map intertwining the generators as a Lie-module hom. -/
def lieHomOfGens (φ : V →ₗ[ℂ] W)
    (hh : ∀ v, φ ⁅sl2_h, v⁆ = ⁅sl2_h, φ v⁆)
    (he : ∀ v, φ ⁅sl2_e, v⁆ = ⁅sl2_e, φ v⁆)
    (hf : ∀ v, φ ⁅sl2_f, v⁆ = ⁅sl2_f, φ v⁆) :
    V →ₗ⁅ℂ,sl2⁆ W :=
  { φ with map_lie' := fun {x v} => map_lie_of_gens φ hh he hf x v }

@[simp] theorem lieHomOfGens_apply (φ : V →ₗ[ℂ] W) (hh he hf) (v : V) :
    lieHomOfGens φ hh he hf v = φ v := rfl

end Intertwine

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
  simp only [cgA, cgB, Fin.val_succ, Fin.val_castSucc,
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

/-! ## The ladder terminates: `F^{ν+1} (cgHW) = 0`

`cgHW λ μ k` is a *primitive vector* (`E`-killed `H`-eigenvector) in Mathlib's sense
(`IsSl2Triple.HasPrimitiveVectorWith`), of eigenvalue the natural number `ν = λ+μ−2k`.
Mathlib's finite-dimensional `sl(2)` theory then forces the lowering ladder to terminate
after exactly `ν+1` steps: `F^{ν+1} (cgHW) = 0`. This is the fact that pins the length of
the irreducible subrep generated by `cgHW λ μ k` to `ν+1 = λ+μ−2k+1`. -/

/-- `cgHW λ μ k` packaged as a Mathlib primitive vector for the standard `sl(2)` triple,
with (natural-number) eigenvalue `ν = λ+μ−2k`. -/
theorem cgHW_hasPrimitiveVectorWith (k : ℕ) (hk : k ≤ min lam mu) :
    IsSl2Triple.HasPrimitiveVectorWith sl2_triple (cgHW lam mu k hk)
      ((lam : ℂ) + mu - 2 * k) where
  ne_zero := cgHW_ne_zero lam mu k hk
  lie_h := lie_sl2_h_cgHW lam mu k hk
  lie_e := lie_sl2_e_cgHW lam mu k hk

/-- **Ladder termination.** Applying the lowering operator `F` to `cgHW λ μ k` one step
past the bottom of the weight ladder kills it: `F^{λ+μ−2k+1} (cgHW λ μ k) = 0`. This is
Mathlib's finite-dimensional `sl(2)` result `pow_toEnd_f_eq_zero_of_eq_nat`, applied to
the primitive vector `cgHW λ μ k` of eigenvalue `λ+μ−2k`. -/
theorem fIter_cgHW_top_eq_zero (k : ℕ) (hk : k ≤ min lam mu) :
    fIter (lam + mu - 2 * k + 1) (cgHW lam mu k hk) = 0 := by
  have hk2 : 2 * k ≤ lam + mu := by omega
  have hcast : ((lam : ℂ) + mu - 2 * k) = ((lam + mu - 2 * k : ℕ) : ℂ) := by
    push_cast [Nat.cast_sub hk2]; ring
  have hzero := (cgHW_hasPrimitiveVectorWith lam mu k hk).pow_toEnd_f_eq_zero_of_eq_nat hcast
  rw [fIter_eq_toEnd_pow]
  exact hzero

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

/-- **The Casimir scalars separate the summands.** For `k, k' ≤ min(λ,μ)` the
Casimir eigenvalues `(λ+μ−2k)(λ+μ−2k+2)/2` agree only when `k = k'`. The map
`ν ↦ ν(ν+2)/2` is injective on `ν ≥ 0`, and here `ν = λ+μ−2k ≥ |λ−μ| ≥ 0`. This
is what lets the Casimir operator pick out the distinct irreducible summands of
`V_λ ⊗ V_μ`. -/
theorem casimir_scalar_inj {k k' : ℕ} (hk : k ≤ min lam mu) (hk' : k' ≤ min lam mu)
    (h : ((lam : ℂ) + mu - 2 * k) * ((lam : ℂ) + mu - 2 * k + 2)
        = ((lam : ℂ) + mu - 2 * k') * ((lam : ℂ) + mu - 2 * k' + 2)) :
    k = k' := by
  -- `a(a+2) − b(b+2) = (a−b)(a+b+2)`, so the difference factors.
  have hfactor :
      (((lam : ℂ) + mu - 2 * k) - ((lam : ℂ) + mu - 2 * k'))
        * (((lam : ℂ) + mu - 2 * k) + ((lam : ℂ) + mu - 2 * k') + 2) = 0 := by
    linear_combination h
  -- `a + b + 2 = (2λ+2μ+2) − (2k+2k') > 0` since `k + k' ≤ λ + μ`, hence nonzero.
  have hsum :
      ((lam : ℂ) + mu - 2 * k) + ((lam : ℂ) + mu - 2 * k') + 2
        = ((2 * lam + 2 * mu + 2 : ℕ) : ℂ) - ((2 * k + 2 * k' : ℕ) : ℂ) := by
    push_cast; ring
  have hpos :
      ((lam : ℂ) + mu - 2 * k) + ((lam : ℂ) + mu - 2 * k') + 2 ≠ 0 := by
    rw [hsum, sub_ne_zero, Ne, Nat.cast_inj]; omega
  -- Therefore `a − b = 0`, i.e. `2k = 2k'`.
  have hab : ((lam : ℂ) + mu - 2 * k) - ((lam : ℂ) + mu - 2 * k') = 0 :=
    (mul_eq_zero.mp hfactor).resolve_right hpos
  have hkk : (k : ℂ) = (k' : ℂ) := by linear_combination (-2⁻¹ : ℂ) * hab
  exact_mod_cast hkk

/-! ## The Clebsch–Gordan ladder

Specializing the general ladder lemmas to the Clebsch–Gordan highest-weight vector
`cgHW λ μ k` (weight `ν = λ+μ−2k`, killed by `E`): the vectors `F^n (cgHW λ μ k)`,
`n = 0,…,λ+μ−2k`, span the irreducible subrep `≅ V_{λ+μ−2k}` generated by `cgHW λ μ k`. -/

/-- `F^n (cgHW λ μ k)` is an `H`-eigenvector of weight `λ+μ−2k − 2n`. -/
theorem lie_sl2_h_fIter_cgHW (k : ℕ) (hk : k ≤ min lam mu) (n : ℕ) :
    ⁅sl2_h, fIter n (cgHW lam mu k hk)⁆
      = ((lam : ℂ) + mu - 2 * k - 2 * n) • fIter n (cgHW lam mu k hk) :=
  lie_sl2_h_fIter ((lam : ℂ) + mu - 2 * k) (cgHW lam mu k hk)
    (lie_sl2_h_cgHW lam mu k hk) n

/-- The raising operator `E` sends `F^{n+1} (cgHW λ μ k)` back to a scalar multiple of
`F^n (cgHW λ μ k)`, with the standard ladder coefficient `(n+1)(λ+μ−2k − n)`. -/
theorem lie_sl2_e_fIter_cgHW (k : ℕ) (hk : k ≤ min lam mu) (n : ℕ) :
    ⁅sl2_e, fIter (n + 1) (cgHW lam mu k hk)⁆
      = (((n : ℂ) + 1) * ((lam : ℂ) + mu - 2 * k - n)) • fIter n (cgHW lam mu k hk) :=
  lie_sl2_e_fIter ((lam : ℂ) + mu - 2 * k) (cgHW lam mu k hk)
    (lie_sl2_e_cgHW lam mu k hk) (lie_sl2_h_cgHW lam mu k hk) n

/-! ## The irreducible subrep `≅ V_{λ+μ−2k}` generated by `cgHW λ μ k`

We assemble the first Clebsch–Gordan deliverable: the cyclic `sl(2)`-submodule of
`V_λ ⊗ V_μ` generated by the highest-weight vector `cgHW λ μ k` is isomorphic to the
irreducible `V_{λ+μ−2k}`.

The intertwiner `cgMap : V_{ν} → V_λ ⊗ V_μ` (`ν = λ+μ−2k`) sends the standard basis
vector `e_n` to `(descFactorial ν n)⁻¹ • F^n (cgHW λ μ k)`. The coefficient is forced by
the requirement that `cgMap` commute with the lowering operator `F`: since in `V_ν` the
operator `F` sends `e_n` to `(ν−n)·e_{n+1}` while on the ladder `F^n(cgHW)` it drops the
factor, the two normalisations differ by `∏_{j<n}(ν−j) = descFactorial ν n`. Ladder
termination `F^{ν+1}(cgHW) = 0` makes the top relation `F·e_ν = 0` hold as well. -/

/-- The identity `Pi.basisFun` and `e_basis` are the same standard basis. -/
theorem basisFun_eq_e_basis (d : ℕ) (n : Fin d) :
    Pi.basisFun ℂ (Fin d) n = e_basis d n := by
  ext j; simp [e_basis, Pi.basisFun_apply, Pi.single_apply]

/-- The recursion satisfied by the Clebsch–Gordan intertwiner coefficients:
`(descFactorial ν (m+1))⁻¹ · (ν − m) = (descFactorial ν m)⁻¹` for `m < ν`. This is the
single scalar identity behind `cgMap` commuting with both `E` and `F`. -/
theorem cgCoeff_rec (nu m : ℕ) (hm : m < nu) :
    (Nat.descFactorial nu (m + 1) : ℂ)⁻¹ * ((nu : ℂ) - m) = (Nat.descFactorial nu m : ℂ)⁻¹ := by
  have hle : m ≤ nu := le_of_lt hm
  have hpos : (Nat.descFactorial nu m : ℂ) ≠ 0 := by
    have := Nat.descFactorial_pos.mpr hle
    exact_mod_cast this.ne'
  have hnm : (nu : ℂ) - m ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => (ne_of_lt hm) ((by exact_mod_cast h : (nu : ℕ) = m).symm)
  rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hle, mul_inv]
  field_simp

variable (lam mu : ℕ)

/-- The Clebsch–Gordan intertwiner `V_{λ+μ−2k} → V_λ ⊗ V_μ`, sending `e_n` to
`(descFactorial ν n)⁻¹ • F^n (cgHW λ μ k)` with `ν = λ+μ−2k`. -/
noncomputable def cgMap (k : ℕ) (hk : k ≤ min lam mu) :
    (Fin (lam + mu - 2 * k + 1) → ℂ) →ₗ[ℂ]
      (Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ) :=
  (Pi.basisFun ℂ (Fin (lam + mu - 2 * k + 1))).constr ℂ
    fun n => ((Nat.descFactorial (lam + mu - 2 * k) (n : ℕ) : ℂ)⁻¹) •
      fIter (n : ℕ) (cgHW lam mu k hk)

theorem cgMap_apply_e_basis (k : ℕ) (hk : k ≤ min lam mu)
    (n : Fin (lam + mu - 2 * k + 1)) :
    cgMap lam mu k hk (e_basis (lam + mu - 2 * k + 1) n)
      = (Nat.descFactorial (lam + mu - 2 * k) (n : ℕ) : ℂ)⁻¹ • fIter (n : ℕ) (cgHW lam mu k hk) := by
  rw [← basisFun_eq_e_basis, cgMap]
  exact (Pi.basisFun ℂ (Fin (lam + mu - 2 * k + 1))).constr_basis ℂ _ n

/-- `cgMap` commutes with the action of `h`. -/
theorem cgMap_lie_h (k : ℕ) (hk : k ≤ min lam mu) (v : Fin (lam + mu - 2 * k + 1) → ℂ) :
    cgMap lam mu k hk ⁅sl2_h, v⁆ = ⁅sl2_h, cgMap lam mu k hk v⁆ := by
  have hcast : (lam : ℂ) + mu - 2 * k = ((lam + mu - 2 * k : ℕ) : ℂ) := by
    have h2 : 2 * k ≤ lam + mu := by omega
    push_cast [Nat.cast_sub h2]; ring
  have key : (cgMap lam mu k hk).comp (LieModule.toEnd ℂ sl2 _ sl2_h)
           = (LieModule.toEnd ℂ sl2 _ sl2_h).comp (cgMap lam mu k hk) := by
    refine (Pi.basisFun ℂ (Fin (lam + mu - 2 * k + 1))).ext fun n => ?_
    simp only [LinearMap.comp_apply, LieModule.toEnd_apply_apply, basisFun_eq_e_basis]
    rw [lie_sl2_h_e_basis, map_smul, cgMap_apply_e_basis, lie_smul, lie_sl2_h_fIter_cgHW,
      smul_smul, smul_smul]
    congr 1
    rw [hcast]; push_cast; ring
  have := LinearMap.congr_fun key v
  simpa only [LinearMap.comp_apply, LieModule.toEnd_apply_apply] using this

/-- `cgMap` commutes with the raising operator `e`. -/
theorem cgMap_lie_e (k : ℕ) (hk : k ≤ min lam mu) (v : Fin (lam + mu - 2 * k + 1) → ℂ) :
    cgMap lam mu k hk ⁅sl2_e, v⁆ = ⁅sl2_e, cgMap lam mu k hk v⁆ := by
  have hcast : (lam : ℂ) + mu - 2 * k = ((lam + mu - 2 * k : ℕ) : ℂ) := by
    have h2 : 2 * k ≤ lam + mu := by omega
    push_cast [Nat.cast_sub h2]; ring
  have key : (cgMap lam mu k hk).comp (LieModule.toEnd ℂ sl2 _ sl2_e)
           = (LieModule.toEnd ℂ sl2 _ sl2_e).comp (cgMap lam mu k hk) := by
    refine (Pi.basisFun ℂ (Fin (lam + mu - 2 * k + 1))).ext fun n => ?_
    simp only [LinearMap.comp_apply, LieModule.toEnd_apply_apply, basisFun_eq_e_basis]
    rcases Nat.eq_zero_or_pos (n : ℕ) with hn0 | hnpos
    · -- bottom: `E` kills `e_0`, and `E` kills `cgHW`.
      have hL : ⁅sl2_e, e_basis (lam + mu - 2 * k + 1) n⁆ = 0 := by
        have h := lie_sl2_e_e_basis (lam + mu - 2 * k + 1) (n : ℕ) n.isLt
        rw [Fin.eta] at h
        rw [h, show ((n : ℕ) : ℂ) = 0 by rw [hn0]; simp, zero_smul]
      rw [hL, map_zero, cgMap_apply_e_basis, lie_smul, hn0, fIter_zero, lie_sl2_e_cgHW,
        smul_zero]
    · -- interior/top: the ladder coefficient plus the coefficient recursion.
      obtain ⟨m, hm⟩ : ∃ m, (n : ℕ) = m + 1 := ⟨(n : ℕ) - 1, by omega⟩
      have hmnu : m < lam + mu - 2 * k := by omega
      have hL : cgMap lam mu k hk ⁅sl2_e, e_basis (lam + mu - 2 * k + 1) n⁆
          = ((n : ℕ) : ℂ) • ((Nat.descFactorial (lam + mu - 2 * k) ((n : ℕ) - 1) : ℂ)⁻¹
              • fIter ((n : ℕ) - 1) (cgHW lam mu k hk)) := by
        have h := lie_sl2_e_e_basis (lam + mu - 2 * k + 1) (n : ℕ) n.isLt
        rw [Fin.eta] at h
        rw [h, map_smul, cgMap_apply_e_basis]
      have hR : ⁅sl2_e, cgMap lam mu k hk (e_basis (lam + mu - 2 * k + 1) n)⁆
          = (Nat.descFactorial (lam + mu - 2 * k) (n : ℕ) : ℂ)⁻¹
              • ⁅sl2_e, fIter (n : ℕ) (cgHW lam mu k hk)⁆ := by
        rw [cgMap_apply_e_basis, lie_smul]
      rw [hL, hR, hm, Nat.add_sub_cancel, lie_sl2_e_fIter_cgHW, smul_smul, smul_smul, hcast]
      congr 1
      have hc := cgCoeff_rec (lam + mu - 2 * k) m hmnu
      rw [← hc]; push_cast; ring
  have := LinearMap.congr_fun key v
  simpa only [LinearMap.comp_apply, LieModule.toEnd_apply_apply] using this

/-- `cgMap` commutes with the lowering operator `f`; ladder termination handles the top. -/
theorem cgMap_lie_f (k : ℕ) (hk : k ≤ min lam mu) (v : Fin (lam + mu - 2 * k + 1) → ℂ) :
    cgMap lam mu k hk ⁅sl2_f, v⁆ = ⁅sl2_f, cgMap lam mu k hk v⁆ := by
  have hcast : (lam : ℂ) + mu - 2 * k = ((lam + mu - 2 * k : ℕ) : ℂ) := by
    have h2 : 2 * k ≤ lam + mu := by omega
    push_cast [Nat.cast_sub h2]; ring
  have key : (cgMap lam mu k hk).comp (LieModule.toEnd ℂ sl2 _ sl2_f)
           = (LieModule.toEnd ℂ sl2 _ sl2_f).comp (cgMap lam mu k hk) := by
    refine (Pi.basisFun ℂ (Fin (lam + mu - 2 * k + 1))).ext fun n => ?_
    simp only [LinearMap.comp_apply, LieModule.toEnd_apply_apply, basisFun_eq_e_basis]
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp n.isLt) with hlt | htop
    · -- interior: `F·e_n = (ν−n)·e_{n+1}`, matched by the coefficient recursion.
      have hL : cgMap lam mu k hk ⁅sl2_f, e_basis (lam + mu - 2 * k + 1) n⁆
          = (((lam + mu - 2 * k + 1 : ℕ) : ℂ) - 1 - (n : ℕ))
              • ((Nat.descFactorial (lam + mu - 2 * k) ((n : ℕ) + 1) : ℂ)⁻¹
                  • fIter ((n : ℕ) + 1) (cgHW lam mu k hk)) := by
        have h := lie_sl2_f_e_basis (lam + mu - 2 * k + 1) (n : ℕ) (by omega)
        rw [Fin.eta] at h
        rw [h, map_smul, cgMap_apply_e_basis]
      have hR : ⁅sl2_f, cgMap lam mu k hk (e_basis (lam + mu - 2 * k + 1) n)⁆
          = (Nat.descFactorial (lam + mu - 2 * k) (n : ℕ) : ℂ)⁻¹
              • fIter ((n : ℕ) + 1) (cgHW lam mu k hk) := by
        rw [cgMap_apply_e_basis, lie_smul, ← fIter_succ]
      rw [hL, hR, smul_smul]
      congr 1
      have hc := cgCoeff_rec (lam + mu - 2 * k) (n : ℕ) hlt
      rw [← hc]; push_cast; ring
    · -- top: `F·e_ν = 0`, and `F·(F^ν cgHW) = F^{ν+1} cgHW = 0`.
      have hL : cgMap lam mu k hk ⁅sl2_f, e_basis (lam + mu - 2 * k + 1) n⁆ = 0 := by
        have h := lie_sl2_f_e_basis_top (lam + mu - 2 * k + 1) (n : ℕ) n.isLt (by omega)
        rw [Fin.eta] at h
        rw [h, map_zero]
      rw [hL, cgMap_apply_e_basis, lie_smul, ← fIter_succ, htop, fIter_cgHW_top_eq_zero,
        smul_zero]
  have := LinearMap.congr_fun key v
  simpa only [LinearMap.comp_apply, LieModule.toEnd_apply_apply] using this

/-- **Clebsch–Gordan intertwiner as a Lie-module hom.** The linear map `cgMap` promoted to
an `sl(2)`-module hom `V_{λ+μ−2k} → V_λ ⊗ V_μ`. -/
noncomputable def cgLieHom (k : ℕ) (hk : k ≤ min lam mu) :
    (Fin (lam + mu - 2 * k + 1) → ℂ) →ₗ⁅ℂ,sl2⁆
      (Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ) :=
  lieHomOfGens (cgMap lam mu k hk) (cgMap_lie_h lam mu k hk) (cgMap_lie_e lam mu k hk)
    (cgMap_lie_f lam mu k hk)

@[simp] theorem cgLieHom_apply (k : ℕ) (hk : k ≤ min lam mu)
    (v : Fin (lam + mu - 2 * k + 1) → ℂ) : cgLieHom lam mu k hk v = cgMap lam mu k hk v := rfl

/-- `cgLieHom` is injective: it is nonzero (`e_0 ↦ cgHW ≠ 0`) out of the irreducible
`V_{λ+μ−2k}`, so its kernel — a Lie submodule of an irreducible — is `⊥`. -/
theorem cgLieHom_injective (k : ℕ) (hk : k ≤ min lam mu) :
    Function.Injective (cgLieHom lam mu k hk) := by
  haveI : NeZero (lam + mu - 2 * k + 1) := ⟨Nat.succ_ne_zero _⟩
  haveI := irrep_isIrreducible (lam + mu - 2 * k + 1)
  rw [← LieModuleHom.ker_eq_bot]
  rcases eq_bot_or_eq_top (cgLieHom lam mu k hk).ker with h | h
  · exact h
  · -- `ker = ⊤` would force `cgLieHom = 0`, but `cgLieHom e_0 = cgHW ≠ 0`.
    exfalso
    have hmem : e_basis (lam + mu - 2 * k + 1) ⟨0, Nat.succ_pos _⟩ ∈ (cgLieHom lam mu k hk).ker :=
      h ▸ trivial
    rw [LieModuleHom.mem_ker, cgLieHom_apply, cgMap_apply_e_basis] at hmem
    simp only [Fin.val_mk, Nat.descFactorial_zero, Nat.cast_one, inv_one, one_smul,
      fIter_zero] at hmem
    exact cgHW_ne_zero lam mu k hk hmem

/-- **Deliverable 1 (Clebsch–Gordan subrep).** The `sl(2)`-submodule of `V_λ ⊗ V_μ`
generated by the highest-weight vector `cgHW λ μ k` (namely the image of `cgLieHom`) is
isomorphic to the `(λ+μ−2k+1)`-dimensional irreducible `V_{λ+μ−2k}`. -/
theorem cgSubrep_iso (k : ℕ) (hk : k ≤ min lam mu) :
    Nonempty ((Fin (lam + mu - 2 * k + 1) → ℂ) ≃ₗ⁅ℂ,sl2⁆
      (LieSubmodule.map (cgLieHom lam mu k hk) ⊤ :
        LieSubmodule ℂ sl2 ((Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ)))) :=
  ⟨(LieModuleEquiv.ofTop (R := ℂ) (L := sl2)
      (M := Fin (lam + mu - 2 * k + 1) → ℂ)).symm.trans
    (LieSubmodule.equivMapOfInjective ⊤ (cgLieHom_injective lam mu k hk))⟩

/-! ## Assembling the full Clebsch–Gordan module isomorphism

We now finish the promotion of the character identity to a module isomorphism. The `k`-th
summand `cgN λ μ k` is the cyclic `sl(2)`-submodule generated by `cgHW λ μ k` (the image of
`cgLieHom`), isomorphic to `V_{λ+μ−2k}` by `cgSubrep_iso`. The two remaining steps are:

* **Independence.** The central Casimir operator `casimir M` acts on `cgN λ μ k` as the
  distinct scalar `s_k = (λ+μ−2k)(λ+μ−2k+2)/2`, so each `cgN λ μ k` lies in a Casimir
  generalized eigenspace, and distinct eigenvalues make these eigenspaces — hence the
  `cgN λ μ k` — `iSupIndep`.
* **Exhaustion.** Independence plus the dimension count `clebsch_gordan_dim`
  `Σ_k (λ+μ−2k+1) = (λ+1)(μ+1) = dim (V_λ ⊗ V_μ)` forces `⨆_k cgN λ μ k = ⊤`, giving the
  internal direct-sum decomposition (`clebsch_gordan_isInternal`) and, combined with the
  per-summand isomorphisms, the full `sl(2)`-module isomorphism
  `V_λ ⊗ V_μ ≅ ⨁_k V_{λ+μ−2k}` (`clebsch_gordan_module_iso`). -/

/-- On the irreducible `V_n = Fin (n+1) → ℂ`, the module structure map `toEnd` is literally
the representation `rhoLieHom`: both send `x ∈ sl(2)` to its action operator. -/
theorem toEnd_irrep (d : ℕ) (x : sl2) :
    LieModule.toEnd ℂ sl2 (Fin d → ℂ) x = rhoLieHom d x := by
  refine LinearMap.ext fun v => ?_
  rw [LieModule.toEnd_apply_apply]
  rfl

/-- The Casimir operator on the irreducible `V_n = Fin (n+1) → ℂ` is the scalar `n(n+2)/2`.
This is `casimir_eq_scalar_lambda` transported from `rhoLieHom` to the generic `casimir`. -/
theorem casimir_irrep (n : ℕ) :
    casimir (Fin (n + 1) → ℂ)
      = (((n : ℂ) * ((n : ℂ) + 2)) / 2) • (1 : Module.End ℂ (Fin (n + 1) → ℂ)) := by
  rw [casimir, toEnd_irrep, toEnd_irrep, toEnd_irrep]
  exact casimir_eq_scalar_lambda n

section CasimirIntertwine

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule sl2 V] [LieModule ℂ sl2 V]
  [AddCommGroup W] [Module ℂ W] [LieRingModule sl2 W] [LieModule ℂ sl2 W]

/-- The Casimir operator is natural in `sl(2)`-module homs: a Lie-module hom `φ : V → W`
commutes with the Casimir operators, `casimir W (φ v) = φ (casimir V v)`. This is because
`casimir` is a polynomial in the structure maps `toEnd h, e, f`, and `φ` intertwines each. -/
theorem casimir_comp_lieHom (φ : V →ₗ⁅ℂ,sl2⁆ W) (v : V) :
    casimir W (φ v) = φ (casimir V v) := by
  simp only [casimir_apply, map_add, map_smul, LieModuleHom.map_lie]

end CasimirIntertwine

variable (lam mu : ℕ)

/-- The Casimir eigenvalue scalar `s_k = (λ+μ−2k)(λ+μ−2k+2)/2` on the `k`-th
Clebsch–Gordan summand. -/
noncomputable def cgCasimirScalar (k : ℕ) : ℂ :=
  ((lam : ℂ) + mu - 2 * k) * ((lam : ℂ) + mu - 2 * k + 2) / 2

/-- The `k`-th **Clebsch–Gordan summand**: the cyclic `sl(2)`-submodule of `V_λ ⊗ V_μ`
generated by the highest-weight vector `cgHW λ μ k` (the image of the intertwiner
`cgLieHom`), isomorphic to `V_{λ+μ−2k}` by `cgSubrep_iso`. Indexed by `k ≤ min(λ,μ)`. -/
noncomputable def cgN (k : Fin (min lam mu + 1)) :
    LieSubmodule ℂ sl2 ((Fin (lam + 1) → ℂ) ⊗[ℂ] (Fin (mu + 1) → ℂ)) :=
  LieSubmodule.map (cgLieHom lam mu (k : ℕ) (Nat.lt_succ_iff.mp k.isLt)) ⊤

/-- Every vector in the `k`-th Clebsch–Gordan summand is a genuine Casimir eigenvector of
eigenvalue `s_k`; hence `cgN λ μ k` sits inside the Casimir generalized eigenspace for `s_k`. -/
theorem cgN_le_casimirGenEigenspace (k : Fin (min lam mu + 1)) :
    cgN lam mu k ≤ casimirGenEigenspace (cgCasimirScalar lam mu (k : ℕ)) := by
  have hk : (k : ℕ) ≤ min lam mu := Nat.lt_succ_iff.mp k.isLt
  have hk2 : 2 * (k : ℕ) ≤ lam + mu := by omega
  have hcast : ((lam : ℂ) + mu - 2 * (k : ℕ)) = ((lam + mu - 2 * (k : ℕ) : ℕ) : ℂ) := by
    push_cast [Nat.cast_sub hk2]; ring
  intro w hw
  simp only [cgN, LieSubmodule.mem_map] at hw
  obtain ⟨v, -, rfl⟩ := hw
  -- `casimir M (cgLieHom v) = cgLieHom (casimir V_ν v) = cgLieHom (s_k • v) = s_k • cgLieHom v`

  have heig : casimir _ (cgLieHom lam mu (k : ℕ) hk v)
      = cgCasimirScalar lam mu (k : ℕ) • cgLieHom lam mu (k : ℕ) hk v := by
    rw [casimir_comp_lieHom, casimir_irrep, LinearMap.smul_apply, Module.End.one_apply,
      map_smul]
    rw [cgCasimirScalar, hcast]
  rw [← LieSubmodule.mem_toSubmodule, casimirGenEigenspace_toSubmodule]
  exact Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr heig)

/-- **Deliverable 2 (independence).** The Clebsch–Gordan summands `cgN λ μ k`,
`k = 0,…,min(λ,μ)`, are `iSupIndep`: they meet pairwise only in `0` and more generally form
an internal direct sum. The separation is by the central Casimir operator, whose eigenvalues
`s_k = (λ+μ−2k)(λ+μ−2k+2)/2` are pairwise distinct (`casimir_scalar_inj`). -/
theorem cgN_iSupIndep : iSupIndep (cgN lam mu) := by
  have hginj : Function.Injective
      (fun k : Fin (min lam mu + 1) => cgCasimirScalar lam mu (k : ℕ)) := by
    intro k k' h
    have hk : (k : ℕ) ≤ min lam mu := Nat.lt_succ_iff.mp k.isLt
    have hk' : (k' : ℕ) ≤ min lam mu := Nat.lt_succ_iff.mp k'.isLt
    apply Fin.ext
    have hprod : ((lam : ℂ) + mu - 2 * (k : ℕ)) * ((lam : ℂ) + mu - 2 * (k : ℕ) + 2)
        = ((lam : ℂ) + mu - 2 * (k' : ℕ)) * ((lam : ℂ) + mu - 2 * (k' : ℕ) + 2) := by
      simp only [cgCasimirScalar] at h
      linear_combination 2 * h
    exact casimir_scalar_inj lam mu hk hk' hprod
  exact ((casimirGenEigenspace_iSupIndep).comp hginj).mono
    (cgN_le_casimirGenEigenspace lam mu)

end Etingof.Sl2Irrep
