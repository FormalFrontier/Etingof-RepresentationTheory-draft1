import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Projective
import EtingofRepresentationTheory.Chapter9.HomologicalDimensionReduction
import EtingofRepresentationTheory.Chapter9.Problem9_4_2

/-!
# Infinite homological dimension of `k[t]/tⁿ` (`n > 1`)

For a field `k` and `n > 1`, the truncated polynomial algebra `R = k[X]/(Xⁿ)` has
**infinite** homological dimension (Problem 9.4.5 (ii), first algebra).

## Strategy

`R` is self-injective and non-semisimple; the residue module has a `2`-periodic minimal
free resolution. Concretely, write `t` for the image of `X` in `R`, and consider the two
cyclic modules

* `A = (t)   = range(·t : R → R)`,
* `B = (tⁿ⁻¹) = range(·tⁿ⁻¹ : R → R)`.

Multiplication by `t` and by `tⁿ⁻¹` gives two short exact sequences (using that `R` is free,
hence projective, and `Ann(t) = (tⁿ⁻¹)`, `Ann(tⁿ⁻¹) = (t)`):

* `0 → B → R → A → 0`   (`·t`),
* `0 → A → R → B → 0`   (`·tⁿ⁻¹`).

By dimension shifting (`Etingof.Problem942.hasProjectiveDimensionLE_syzygy`) `pd(A) ≤ d`
(`d > 0`) forces `pd(B) ≤ d - 1`, and symmetrically. Since neither `A` nor `B` is projective
(a splitting would force `tⁿ⁻¹ = 0`), a symmetric induction shows `pd(A) = pd(B) = ∞`, so `A`
witnesses `¬ HasHomologicalDimensionLE R d` for every `d`, whence
`homologicalDimension R = ⊤` by `Etingof.homologicalDimension_eq_top`.
-/

universe u

open Polynomial CategoryTheory

namespace Etingof.TruncatedPoly

variable (k : Type u) [Field k] (n : ℕ)

/-- The truncated polynomial algebra `R = k[X]/(Xⁿ)`. -/
abbrev Rq : Type u := k[X] ⧸ Ideal.span {(X : k[X]) ^ n}

/-- The image `t` of `X` in `R = k[X]/(Xⁿ)`. -/
noncomputable def tq : Rq k n := Ideal.Quotient.mk (Ideal.span {(X : k[X]) ^ n}) X

/-- `tⁿ = 0` in `R = k[X]/(Xⁿ)`. -/
theorem tq_pow_n : (tq k n) ^ n = 0 := by
  rw [tq, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

/-- `tⁿ⁻¹ ≠ 0` in `R = k[X]/(Xⁿ)` (for `n ≥ 1`). -/
theorem tq_pow_pred_ne (hn : 0 < n) : (tq k n) ^ (n - 1) ≠ 0 := by
  rw [tq, ← map_pow]
  intro h
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h
  -- h : X^n ∣ X^(n-1)
  have hne : (X : k[X]) ^ (n - 1) ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
  have := Polynomial.natDegree_le_of_dvd h hne
  simp only [Polynomial.natDegree_X_pow] at this
  omega

/-- `Ann(t) = (tⁿ⁻¹)`: the kernel of `·t` equals the range of `·tⁿ⁻¹`. -/
theorem ker_mulLeft_t (hn : 0 < n) :
    LinearMap.ker (LinearMap.mulLeft (Rq k n) (tq k n)) =
      LinearMap.range (LinearMap.mulLeft (Rq k n) ((tq k n) ^ (n - 1))) := by
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker, LinearMap.mulLeft_apply] at hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [LinearMap.mem_range]
    have hmul : (tq k n) * (Ideal.Quotient.mk (Ideal.span {(X : k[X]) ^ n}) p)
        = Ideal.Quotient.mk _ (X * p) := by rw [tq]; exact (map_mul _ _ _).symm
    rw [hmul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx
    have hsplit : (X : k[X]) ^ n = X * X ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ']
    rw [hsplit, mul_dvd_mul_iff_left (Polynomial.X_ne_zero)] at hx
    obtain ⟨q, hq⟩ := hx
    refine ⟨Ideal.Quotient.mk _ q, ?_⟩
    rw [LinearMap.mulLeft_apply, tq, ← map_pow, ← map_mul, ← hq]
  · rintro _ ⟨r, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, ← mul_assoc,
      ← pow_succ', show (n - 1) + 1 = n by omega, tq_pow_n, zero_mul]

/-- `Ann(tⁿ⁻¹) = (t)`: the kernel of `·tⁿ⁻¹` equals the range of `·t`. -/
theorem ker_mulLeft_t_pow (hn : 0 < n) :
    LinearMap.ker (LinearMap.mulLeft (Rq k n) ((tq k n) ^ (n - 1))) =
      LinearMap.range (LinearMap.mulLeft (Rq k n) (tq k n)) := by
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker, LinearMap.mulLeft_apply] at hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [LinearMap.mem_range]
    have hmul : (tq k n) ^ (n - 1) * (Ideal.Quotient.mk (Ideal.span {(X : k[X]) ^ n}) p)
        = Ideal.Quotient.mk _ (X ^ (n - 1) * p) := by
      rw [tq, ← map_pow]; exact (map_mul _ _ _).symm
    rw [hmul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx
    have hsplit : (X : k[X]) ^ n = X ^ (n - 1) * X := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    have hne : (X : k[X]) ^ (n - 1) ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
    rw [hsplit, mul_dvd_mul_iff_left hne] at hx
    obtain ⟨q, hq⟩ := hx
    refine ⟨Ideal.Quotient.mk _ q, ?_⟩
    rw [LinearMap.mulLeft_apply, tq, ← map_mul, ← hq]
  · rintro _ ⟨r, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, ← mul_assoc,
      ← pow_succ, show (n - 1) + 1 = n by omega, tq_pow_n, zero_mul]

/-- `tⁿ⁻¹ · tⁿ⁻¹ = 0` for `n > 1` (since `2(n-1) ≥ n`). -/
theorem tq_pow_pred_mul_self (hn : 1 < n) :
    (tq k n) ^ (n - 1) * (tq k n) ^ (n - 1) = 0 := by
  rw [← pow_add]
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (show n ≤ (n - 1) + (n - 1) by omega)
  rw [hm, pow_add, tq_pow_n, zero_mul]

end Etingof.TruncatedPoly
