import EtingofRepresentationTheory.Chapter2.Problem2_15_1_m_Module

/-!
# The maximal generalized weight space (Problem 2.15.1(a)--(e))

This file supplies the generalized-weight-space beginning of Etingof's elementary proof of
complete reducibility for finite-dimensional `sl(2)`-modules.

The first two parts are formalized here at their source generality:

* `lie_e_eq_zero_on_maxGenEigenspace` proves part (a), in the intrinsic form that if
  `lambda + 2` is not an eigenvalue of `H`, then `E` vanishes on the entire generalized
  `lambda`-eigenspace of `H`.  The proof uses the identity
  `(H - (lambda+2))^k E = E (H-lambda)^k`.
* `eIter_fIter_eq_aeval_highestWeightPolynomial` proves part (b) for an arbitrary vector
  killed by `E` (with no eigenvector assumption).  The polynomial is defined recursively by
  `P_0 = 1` and `P_{k+1}(X) = (k+1) P_k(X) (X-k)`, and has degree exactly `k`.

Parts (c)--(e), which use finite-dimensionality to prove termination of every lowering ladder,
diagonalize `H` on the maximal generalized weight space, and identify the least termination
index, build on these endpoints and remain separate follow-up work.
-/

open Etingof Etingof.Sl2Irrep
open LieModule Module Polynomial

namespace Etingof.Sl2Irrep

section MaximalGeneralizedWeight

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
  [LieRingModule sl2 M] [LieModule ℂ sl2 M]

private noncomputable abbrev H : Module.End ℂ M := LieModule.toEnd ℂ sl2 M sl2_h
private noncomputable abbrev E : Module.End ℂ M := LieModule.toEnd ℂ sl2 M sl2_e

/-- The shifted intertwining identity `(H-(lambda+2)) E = E (H-lambda)`. -/
private theorem h_sub_mul_e_apply (lambda : ℂ) (v : M) :
    (H (M := M) - (lambda + 2) • 1) (E (M := M) v) =
      E (M := M) ((H (M := M) - lambda • 1) v) := by
  change ⁅sl2_h, ⁅sl2_e, v⁆⁆ - (lambda + 2) • ⁅sl2_e, v⁆ =
    ⁅sl2_e, ⁅sl2_h, v⁆ - lambda • v⁆
  rw [leibniz_lie sl2_h sl2_e v, lie_h_e, nsmul_lie, lie_sub, lie_smul]
  module

/-- Iterating the shifted intertwining identity gives
`(H-(lambda+2))^k E = E (H-lambda)^k`. -/
private theorem h_sub_pow_e_apply (lambda : ℂ) (k : ℕ) (v : M) :
    ((H (M := M) - (lambda + 2) • 1) ^ k) (E (M := M) v) =
      E (M := M) (((H (M := M) - lambda • 1) ^ k) v) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, h_sub_mul_e_apply]
      congr 1
      rw [← Module.End.mul_apply, ← pow_succ']

/-- **Problem 2.15.1(a), generalized-eigenspace form.**
If `lambda + 2` is not an eigenvalue of `H`, then the raising operator `E` vanishes on the
entire maximal generalized `lambda`-eigenspace of `H`.

Choosing `lambda` among the eigenvalues with maximal real part supplies the hypothesis in the
book.  This statement isolates the algebraic content and avoids baking a particular ordering
construction for the finite spectrum into the theorem. -/
theorem lie_e_eq_zero_on_maxGenEigenspace (lambda : ℂ)
    (hmax : ¬ (H (M := M)).HasEigenvalue (lambda + 2))
    {v : M} (hv : v ∈ (H (M := M)).maxGenEigenspace lambda) :
    ⁅sl2_e, v⁆ = 0 := by
  rw [Module.End.mem_maxGenEigenspace] at hv
  obtain ⟨k, hk⟩ := hv
  by_contra hne
  apply hmax
  apply Module.End.hasEigenvalue_of_hasGenEigenvalue (k := k)
  intro hbot
  have hmem : ⁅sl2_e, v⁆ ∈
      (H (M := M)).genEigenspace (lambda + 2) k := by
    rw [Module.End.mem_genEigenspace_nat, LinearMap.mem_ker]
    change ((H (M := M) - (lambda + 2) • 1) ^ k) (E (M := M) v) = 0
    rw [h_sub_pow_e_apply (M := M), hk, map_zero]
  have : ⁅sl2_e, v⁆ ∈ (⊥ : Submodule ℂ M) := hbot ▸ hmem
  exact hne (by simpa using this)

end MaximalGeneralizedWeight

section HighestWeightPolynomial

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
  [LieRingModule sl2 M] [LieModule ℂ sl2 M]

/-- The iterated raising operator `E^n`. -/
noncomputable def eIter (n : ℕ) (w : M) : M :=
  ((LieModule.toEnd ℂ sl2 M sl2_e) ^ n) w

@[simp] theorem eIter_zero (w : M) : eIter 0 w = w := by simp [eIter]

theorem eIter_succ (n : ℕ) (w : M) :
    eIter (n + 1) w = eIter n ⁅sl2_e, w⁆ := by
  simp only [eIter, pow_succ, Module.End.mul_apply, LieModule.toEnd_apply_apply]

/-- The polynomial in Problem 2.15.1(b):
`P_0 = 1`, `P_{k+1}(X) = (k+1) P_k(X) (X-k)`.

Thus `P_k(X) = k! X(X-1)...(X-k+1)`. -/
noncomputable def highestWeightPolynomial : ℕ → Polynomial ℂ
  | 0 => 1
  | k + 1 => C (k + 1 : ℂ) * highestWeightPolynomial k * (X - C (k : ℂ))

@[simp] theorem highestWeightPolynomial_zero : highestWeightPolynomial 0 = 1 := rfl

theorem highestWeightPolynomial_succ (k : ℕ) :
    highestWeightPolynomial (k + 1) =
      C (k + 1 : ℂ) * highestWeightPolynomial k * (X - C (k : ℂ)) := rfl

theorem highestWeightPolynomial_ne_zero (k : ℕ) : highestWeightPolynomial k ≠ 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [highestWeightPolynomial_succ]
      exact mul_ne_zero (mul_ne_zero (C_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero k)) ih)
        (X_sub_C_ne_zero (k : ℂ))

/-- The polynomial `P_k` in part (b) has degree exactly `k`. -/
theorem highestWeightPolynomial_natDegree (k : ℕ) :
    (highestWeightPolynomial k).natDegree = k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [highestWeightPolynomial_succ,
        natDegree_mul (mul_ne_zero
          (C_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero k))
          (highestWeightPolynomial_ne_zero k))
          (X_sub_C_ne_zero (k : ℂ)),
        natDegree_mul (C_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero k))
          (highestWeightPolynomial_ne_zero k),
        natDegree_C, ih, natDegree_X_sub_C]
      omega

/-- The general weight-shift identity
`H F^k w = F^k H w - 2k F^k w`. -/
theorem lie_sl2_h_fIter_general (k : ℕ) (w : M) :
    ⁅sl2_h, fIter k w⁆ =
      fIter k ⁅sl2_h, w⁆ - (2 * k : ℂ) • fIter k w := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [fIter_succ, leibniz_lie sl2_h sl2_f, lie_h_f, ih,
        neg_lie, nsmul_lie, lie_sub, lie_smul]
      simp only [show ∀ u : M, ⁅sl2_f, fIter k u⁆ = fIter (k + 1) u from
        fun u => (fIter_succ k u).symm]
      push_cast
      module

/-- Applying `F^n` intertwines `H-lambda` with `H-(lambda-2n)`. -/
private theorem h_shift_fIter_apply (lambda : ℂ) (n : ℕ) (w : M) :
    ((LieModule.toEnd ℂ sl2 M sl2_h - (lambda - 2 * n) • 1) (fIter n w)) =
      fIter n ((LieModule.toEnd ℂ sl2 M sl2_h - lambda • 1) w) := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    LieModule.toEnd_apply_apply]
  rw [lie_sl2_h_fIter_general]
  simp only [fIter_eq_toEnd_pow, map_sub, map_smul]
  module

/-- The iterated shifted intertwining identity
`(H-(lambda-2n))^k F^n = F^n (H-lambda)^k`. -/
private theorem h_shift_pow_fIter_apply (lambda : ℂ) (n k : ℕ) (w : M) :
    ((LieModule.toEnd ℂ sl2 M sl2_h - (lambda - 2 * n) • 1) ^ k) (fIter n w) =
      fIter n (((LieModule.toEnd ℂ sl2 M sl2_h - lambda • 1) ^ k) w) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, h_shift_fIter_apply]
      congr 1
      rw [← Module.End.mul_apply, ← pow_succ']

/-- Applying `F^n` sends the generalized `lambda`-weight space into the generalized
`lambda-2n`-weight space. -/
theorem fIter_mem_maxGenEigenspace (lambda : ℂ) {w : M}
    (hw : w ∈ (LieModule.toEnd ℂ sl2 M sl2_h).maxGenEigenspace lambda) (n : ℕ) :
    fIter n w ∈ (LieModule.toEnd ℂ sl2 M sl2_h).maxGenEigenspace
      (lambda - 2 * n) := by
  rw [Module.End.mem_maxGenEigenspace] at hw ⊢
  obtain ⟨k, hk⟩ := hw
  refine ⟨k, ?_⟩
  rw [h_shift_pow_fIter_apply, hk]
  simp only [fIter_eq_toEnd_pow, map_zero]

/-- **Problem 2.15.1(c).** Every vector in a generalized `H`-eigenspace has a terminating
lowering ladder: `F^N v = 0` for some positive `N`.

Indeed, if all `F^n v` were nonzero, they would lie in the pairwise independent generalized
eigenspaces of weights `lambda-2n`, producing an infinite linearly independent family in a
finite-dimensional space. -/
theorem exists_pos_fIter_eq_zero_of_mem_maxGenEigenspace [FiniteDimensional ℂ M]
    (lambda : ℂ) {v : M}
    (hv : v ∈ (LieModule.toEnd ℂ sl2 M sl2_h).maxGenEigenspace lambda) :
    ∃ N : ℕ, 0 < N ∧ fIter N v = 0 := by
  by_cases hv0 : v = 0
  · exact ⟨1, by omega, by simp [hv0, fIter_eq_toEnd_pow]⟩
  by_contra htermination
  push Not at htermination
  have hnonzero : ∀ n : ℕ, fIter n v ≠ 0 := by
    intro n
    rcases n with _ | n
    · simpa using hv0
    · exact htermination (n + 1) (by omega)
  have hweight : Function.Injective (fun n : ℕ => lambda - 2 * (n : ℂ)) := by
    intro a b hab
    have hmul : (2 : ℂ) * (a : ℂ) = 2 * (b : ℂ) :=
      neg_injective (add_left_cancel
        (show lambda + -(2 * (a : ℂ)) = lambda + -(2 * (b : ℂ)) by
          simpa only [sub_eq_add_neg] using hab))
    have hcast : (a : ℂ) = (b : ℂ) :=
      mul_left_cancel₀ (two_ne_zero (α := ℂ)) hmul
    exact_mod_cast hcast
  have hli : LinearIndependent ℂ (fun n : ℕ => fIter n v) :=
    ((Module.End.independent_maxGenEigenspace
      (LieModule.toEnd ℂ sl2 M sl2_h)).comp hweight).linearIndependent _
      (fun n => fIter_mem_maxGenEigenspace lambda hv n) hnonzero
  exact Module.Finite.not_linearIndependent_of_infinite
    (fun n : ℕ => fIter n v) hli

/-- The general commutation identity
`E F^(k+1) w = F^(k+1) E w + (k+1) F^k (H-k) w`.

Unlike `lie_sl2_e_fIter`, this requires neither `E w = 0` nor that `w` be an `H`-eigenvector.
It is the induction engine for Problem 2.15.1(b). -/
theorem lie_sl2_e_fIter_general (k : ℕ) (w : M) :
    ⁅sl2_e, fIter (k + 1) w⁆ =
      fIter (k + 1) ⁅sl2_e, w⁆ +
        (k + 1 : ℂ) • fIter k (⁅sl2_h, w⁆ - (k : ℂ) • w) := by
  induction k with
  | zero =>
      rw [fIter_succ, fIter_zero, leibniz_lie sl2_e sl2_f, lie_e_f]
      rw [fIter_succ, fIter_zero]
      simp
      abel
  | succ k ih =>
      rw [fIter_succ, leibniz_lie sl2_e sl2_f, lie_e_f, ih,
        lie_add, lie_smul, lie_sl2_h_fIter_general]
      simp only [show ∀ u : M, ⁅sl2_f, fIter (k + 1) u⁆ = fIter (k + 2) u from
        fun u => by simpa [Nat.add_assoc] using (fIter_succ (k + 1) u).symm,
        show ∀ u : M, ⁅sl2_f, fIter k u⁆ = fIter (k + 1) u from
        fun u => (fIter_succ k u).symm]
      simp only [fIter_eq_toEnd_pow, map_sub, map_smul]
      push_cast
      module

/-- **Problem 2.15.1(b).** If `Ew = 0`, then
`E^k F^k w = P_k(H)w`, where `P_k` is the degree-`k` polynomial
`k! X(X-1)...(X-k+1)`.

The statement has the source's full generality: `w` need not be an eigenvector and `M` need
not be finite-dimensional. -/
theorem eIter_fIter_eq_aeval_highestWeightPolynomial (k : ℕ) (w : M)
    (hE : ⁅sl2_e, w⁆ = 0) :
    eIter k (fIter k w) =
      Polynomial.aeval (LieModule.toEnd ℂ sl2 M sl2_h) (highestWeightPolynomial k) w := by
  induction k generalizing w with
  | zero => simp [highestWeightPolynomial, eIter]
  | succ k ih =>
      rw [eIter_succ, lie_sl2_e_fIter_general, hE]
      have hfzero : fIter (k + 1) (0 : M) = 0 := by
        rw [fIter_eq_toEnd_pow, map_zero]
      rw [hfzero, zero_add]
      change ((LieModule.toEnd ℂ sl2 M sl2_e) ^ k)
          ((k + 1 : ℂ) • fIter k (⁅sl2_h, w⁆ - (k : ℂ) • w)) = _
      rw [map_smul]
      change (k + 1 : ℂ) • eIter k
          (fIter k (⁅sl2_h, w⁆ - (k : ℂ) • w)) = _
      rw [ih]
      · rw [highestWeightPolynomial_succ, map_mul, map_mul, Polynomial.aeval_C]
        have heval : Polynomial.aeval (LieModule.toEnd ℂ sl2 M sl2_h)
            (X - C (k : ℂ)) =
            LieModule.toEnd ℂ sl2 M sl2_h -
              algebraMap ℂ (Module.End ℂ M) (k : ℂ) := by
          rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
        rw [heval]
        simp only [Module.End.mul_apply, Module.algebraMap_end_apply,
          LinearMap.sub_apply,
          map_sub, map_smul, LieModule.toEnd_apply_apply]
        module
      · rw [lie_sub, lie_smul, hE]
        have heh : ⁅sl2_e, sl2_h⁆ = -(2 • sl2_e) := by
          rw [(lie_skew sl2_e sl2_h).symm, lie_h_e]
        have hEHw : ⁅sl2_e, ⁅sl2_h, w⁆⁆ = 0 := by
          rw [leibniz_lie, heh, neg_lie, nsmul_lie, hE, lie_zero]
          simp
        simpa using hEHw

/-- **Problem 2.15.1(e), least-exponent calculation.**
Let `v` be a nonzero highest-weight vector of weight `lambda`, and let `N > 0` be the first
positive exponent for which `F^N v = 0`. Then `lambda = N-1`.

Part (d) supplies the eigenvector hypothesis for vectors in the maximal generalized weight
space; this theorem isolates the exact final calculation from the ladder identity. -/
theorem highestWeight_eq_nat_of_minimal_fIter_zero (lambda : ℂ) (v : M) (N : ℕ)
    (_hv : v ≠ 0) (hE : ⁅sl2_e, v⁆ = 0) (hH : ⁅sl2_h, v⁆ = lambda • v)
    (hNpos : 0 < N) (hN : fIter N v = 0)
    (hmin : ∀ m : ℕ, m < N → fIter m v ≠ 0) :
    lambda = (N - 1 : ℕ) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hraise := lie_sl2_e_fIter lambda v hE hH n
  rw [hN, lie_zero] at hraise
  have hscalar : ((n : ℂ) + 1) * (lambda - n) = 0 := by
    exact (smul_eq_zero.mp hraise.symm).resolve_right (hmin n (by omega))
  have hfirst : (n : ℂ) + 1 ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hlambda : lambda - (n : ℂ) = 0 :=
    (mul_eq_zero.mp hscalar).resolve_left hfirst
  have : lambda = (n : ℂ) := sub_eq_zero.mp hlambda
  simpa using this

end HighestWeightPolynomial

end Etingof.Sl2Irrep
