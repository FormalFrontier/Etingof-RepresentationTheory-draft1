import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Data.Nat.Factorial.Basic
import EtingofRepresentationTheory.Chapter2.Sl2Irrep

/-!
# Jacobson–Morozov for a single Jordan block (Problem 2.15.1(l))

Part (l) of Etingof Problem 2.15.1 is the `sl(2)` special case of the
Jacobson–Morozov lemma: for a finite dimensional complex vector space `V` and a
nilpotent operator `A : V → V`, there is a representation of `sl(2)` on `V` with
`E = A`, unique up to isomorphism. The book's route is: put `A` in Jordan normal
form, give each nilpotent Jordan block `J_{0,n}` an `sl(2)`-structure coming from
the irreducible `V_n`, and assemble the direct sum; uniqueness then follows from
the classification of representations (part (f)).

This file formalizes the **constructive heart** of that argument: the single
Jordan block. We exhibit, for every `n`, an `sl(2)`-representation on `V_n =
Fin n → ℂ` whose raising operator `E = ρ(e)` is *exactly* the standard nilpotent
Jordan shift `J_{0,n}` (`e_i ↦ e_{i-1}`, `e_0 ↦ 0`).

The representation is obtained by conjugating the irreducible representation
`rhoLieHom n` (from `Sl2Irrep.lean`) by the diagonal rescaling `e_k ↦ k! · e_k`.
On `V_n`, `ρ(e)` already acts as the shift `e_k ↦ k · e_{k-1}` with nonzero
coefficients, so it is a single Jordan block; the factorial rescaling normalises
those coefficients to `1`, turning `ρ(e)` into the standard shift `J_{0,n}`.

## Scope

This is part (l) for a single block. The two remaining pieces — assembling an
arbitrary nilpotent `A` (via its Jordan decomposition into blocks) into an
`sl(2)`-representation with `E = A`, and uniqueness up to isomorphism via the
classification (f) — are tracked as follow-up issues. Mathlib does not currently
provide an explicit Jordan-basis decomposition of a nilpotent endomorphism, which
is the missing ingredient for the general assembly.
-/

open Etingof
open Etingof.Sl2Irrep

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Etingof.Sl2Irrep

/-! ## The standard nilpotent Jordan block -/

/-- The standard nilpotent Jordan block `J_{0,n}` on `V_n = Fin n → ℂ`:
`(J v)_k = v_{k+1}` (with `v_n = 0`), i.e. `J e_i = e_{i-1}` and `J e_0 = 0`. -/
noncomputable def jordanShift (n : ℕ) : Module.End ℂ (Fin n → ℂ) where
  toFun v k := if h : (k : ℕ) + 1 < n then v ⟨(k : ℕ) + 1, h⟩ else 0
  map_add' u w := by ext k; simp only [Pi.add_apply]; split <;> simp
  map_smul' c v := by
    ext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split <;> simp

theorem jordanShift_apply (n : ℕ) (v : Fin n → ℂ) (k : Fin n) :
    jordanShift n v k = if h : (k : ℕ) + 1 < n then v ⟨(k : ℕ) + 1, h⟩ else 0 := rfl

/-- Action of `J_{0,n}` on a basis vector: `J e_k = e_{k-1}` for `k ≥ 1`, `0` else. -/
theorem jordanShift_e_basis (n : ℕ) (k : Fin n) :
    jordanShift n (e_basis n k)
      = if h : 0 < (k : ℕ) then e_basis n ⟨(k : ℕ) - 1, by omega⟩ else 0 := by
  ext j
  rw [jordanShift_apply]
  by_cases hk : 0 < (k : ℕ)
  · simp only [hk, dite_true]
    by_cases hj : (j : ℕ) + 1 < n
    · simp only [hj, dite_true, e_basis_apply, Fin.ext_iff]
      by_cases hjk : (j : ℕ) + 1 = (k : ℕ)
      · rw [if_pos hjk, if_pos (by omega)]
      · rw [if_neg hjk, if_neg (by omega)]
    · simp only [hj, dite_false, e_basis_apply, Fin.ext_iff]
      rw [if_neg (by omega)]
  · simp only [hk, dite_false, Pi.zero_apply]
    by_cases hj : (j : ℕ) + 1 < n
    · simp only [hj, dite_true, e_basis_apply, Fin.ext_iff]
      rw [if_neg (by omega)]
    · simp only [hj, dite_false]

/-! ## Nilpotency of the Jordan block -/

/-- Powers of the shift: `(J^m v)_k = v_{k+m}` (with out-of-range entries `0`). -/
theorem jordanShift_pow_apply (n m : ℕ) (v : Fin n → ℂ) (k : Fin n) :
    (jordanShift n ^ m) v k
      = if h : (k : ℕ) + m < n then v ⟨(k : ℕ) + m, h⟩ else 0 := by
  induction m generalizing k with
  | zero =>
    simp only [pow_zero, Module.End.one_apply, Nat.add_zero]
    rw [dif_pos k.isLt]
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, jordanShift_apply]
    by_cases hk1 : (k : ℕ) + 1 < n
    · rw [dif_pos hk1, ih ⟨(k : ℕ) + 1, hk1⟩]
      by_cases hkm : (k : ℕ) + 1 + m < n
      · rw [dif_pos hkm, dif_pos (by omega)]
        exact congrArg v (Fin.ext (show (k : ℕ) + 1 + m = (k : ℕ) + (m + 1) by omega))
      · rw [dif_neg hkm, dif_neg (by omega)]
    · rw [dif_neg hk1, dif_neg (by omega)]

/-- The Jordan block `J_{0,n}` is nilpotent: `J^n = 0`. -/
theorem jordanShift_pow_eq_zero (n : ℕ) : jordanShift n ^ n = 0 := by
  apply LinearMap.ext
  intro v
  funext k
  rw [jordanShift_pow_apply, dif_neg (by omega), LinearMap.zero_apply, Pi.zero_apply]

theorem jordanShift_isNilpotent (n : ℕ) : IsNilpotent (jordanShift n) :=
  ⟨n, jordanShift_pow_eq_zero n⟩

/-! ## The diagonal factorial rescaling -/

/-- The diagonal rescaling `e_k ↦ k! · e_k` of `V_n`, a linear automorphism. -/
noncomputable def factScale (n : ℕ) : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) where
  toFun v k := ((k : ℕ).factorial : ℂ) * v k
  map_add' u w := by ext k; simp [mul_add]
  map_smul' c v := by ext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
  invFun v k := (((k : ℕ).factorial : ℂ))⁻¹ * v k
  left_inv v := by
    ext k
    have hfac : ((k : ℕ).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
  right_inv v := by
    ext k
    have hfac : ((k : ℕ).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp

theorem factScale_apply (n : ℕ) (v : Fin n → ℂ) (k : Fin n) :
    factScale n v k = ((k : ℕ).factorial : ℂ) * v k := rfl

theorem factScale_symm_apply (n : ℕ) (v : Fin n → ℂ) (k : Fin n) :
    (factScale n).symm v k = (((k : ℕ).factorial : ℂ))⁻¹ * v k := rfl

/-- `factScale` scales the basis vector `e_k` by `k!`. -/
theorem factScale_e_basis (n : ℕ) (k : Fin n) :
    factScale n (e_basis n k) = ((k : ℕ).factorial : ℂ) • e_basis n k := by
  ext j
  rw [factScale_apply, Pi.smul_apply, smul_eq_mul, e_basis_apply]
  by_cases hjk : j = k
  · subst hjk; simp
  · simp [hjk]

/-- `factScale.symm` scales the basis vector `e_k` by `(k!)⁻¹`. -/
theorem factScale_symm_e_basis (n : ℕ) (k : Fin n) :
    (factScale n).symm (e_basis n k) = (((k : ℕ).factorial : ℂ))⁻¹ • e_basis n k := by
  ext j
  rw [factScale_symm_apply, Pi.smul_apply, smul_eq_mul, e_basis_apply]
  by_cases hjk : j = k
  · subst hjk; simp
  · simp [hjk]

/-! ## The single-block `sl(2)`-representation -/

/-- The `sl(2)`-representation on `V_n` obtained by conjugating the irreducible
representation `rhoLieHom n` by the factorial rescaling `factScale n`. Its raising
operator `ρ(e)` is the standard Jordan block `J_{0,n}` (see `sl2RepOfBlock_e`). -/
noncomputable def sl2RepOfBlock (n : ℕ) : sl2 →ₗ⁅ℂ⁆ Module.End ℂ (Fin n → ℂ) :=
  ((factScale n).conjAlgEquiv ℂ : _ →ₐ[ℂ] _).toLieHom.comp (rhoLieHom n)

theorem sl2RepOfBlock_apply (n : ℕ) (x : sl2) :
    sl2RepOfBlock n x = (factScale n).conjAlgEquiv ℂ (rhoLieHom n x) := rfl

/-- **Single-block Jacobson–Morozov (Problem 2.15.1(l)).** On `V_n = Fin n → ℂ`
the representation `sl2RepOfBlock n` sends the standard generator `e` to the
standard nilpotent Jordan block `J_{0,n}`. Equivalently: every single Jordan block
carries an `sl(2)`-structure with `E` equal to that block. -/
theorem sl2RepOfBlock_e (n : ℕ) : sl2RepOfBlock n sl2_e = jordanShift n := by
  refine (Pi.basisFun ℂ (Fin n)).ext fun k => ?_
  rw [Pi.basisFun_apply]
  change sl2RepOfBlock n sl2_e (e_basis n k) = jordanShift n (e_basis n k)
  -- the action of `ρ(e)` on a basis vector, via the public API of `Sl2Irrep`
  have he : rhoLieHom n sl2_e (e_basis n k)
      = ((k : ℕ) : ℂ) • e_basis n ⟨(k : ℕ) - 1, by omega⟩ := by
    have h := lie_sl2_e_e_basis n (k : ℕ) k.isLt
    rw [Fin.eta] at h
    rw [← lie_eq_rhoLieHom]
    exact h
  rw [sl2RepOfBlock_apply, LinearEquiv.conjAlgEquiv_apply]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [factScale_symm_e_basis, map_smul, he]
  simp only [map_smul, factScale_e_basis]
  rw [jordanShift_e_basis]
  by_cases hk : 0 < (k : ℕ)
  · rw [dif_pos hk, smul_smul, smul_smul]
    -- scalar (k!)⁻¹ * k * (k-1)! = 1
    have hscalar : (((k : ℕ).factorial : ℂ))⁻¹ * ((k : ℕ) : ℂ)
        * (((k : ℕ) - 1).factorial : ℂ) = 1 := by
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : (k : ℕ) ≠ 0)
      rw [hm, Nat.factorial_succ]
      have hm1 : ((m : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
      have hmf : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      push_cast
      field_simp
    rw [hscalar, one_smul]
  · rw [dif_neg hk]
    have hk0 : (k : ℕ) = 0 := by omega
    simp [hk0]

/-- **Existence for a single block.** For every `n`, there is an
`sl(2)`-representation on `V_n` whose `E` operator is the standard nilpotent
Jordan block `J_{0,n}`. -/
theorem exists_sl2Rep_jordanShift (n : ℕ) :
    ∃ ρ : sl2 →ₗ⁅ℂ⁆ Module.End ℂ (Fin n → ℂ), ρ sl2_e = jordanShift n :=
  ⟨sl2RepOfBlock n, sl2RepOfBlock_e n⟩

end Etingof.Sl2Irrep
