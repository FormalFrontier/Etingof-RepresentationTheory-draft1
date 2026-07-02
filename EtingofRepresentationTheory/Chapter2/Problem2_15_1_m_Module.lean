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

/-- Any element of `sl(2)` decomposes on the standard triple:
`X = X₀₀ • h + X₀₁ • e + X₁₀ • f`. -/
theorem sl2_decomp (X : sl2) :
    X = X.val 0 0 • sl2_h + X.val 0 1 • sl2_e + X.val 1 0 • sl2_f := by
  apply Subtype.ext
  have htr : X.val 1 1 = -X.val 0 0 := sl2_traceless X
  ext i j
  show X.val i j
    = (X.val 0 0 • sl2_h.val + X.val 0 1 • sl2_e.val + X.val 1 0 • sl2_f.val) i j
  fin_cases i <;> fin_cases j <;>
    simp only [sl2_h, sl2_e, sl2_f, LieAlgebra.SpecialLinear.val_single,
      LieAlgebra.SpecialLinear.val_singleSubSingle, Matrix.add_apply, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.single, smul_eq_mul] <;>
    simp [htr]

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

end Etingof.Sl2Irrep
