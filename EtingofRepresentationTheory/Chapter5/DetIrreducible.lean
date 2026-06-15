import Mathlib
import EtingofRepresentationTheory.Chapter5.DetLocalization

/-!
# Irreducibility and primeness of the generic determinant polynomial

This file works towards `Irreducible (detPoly k N)` and `Prime (detPoly k N)`
for `N ≥ 1`, where
`detPoly k N = Matrix.det (Matrix.mvPolynomialX (Fin N) (Fin N) k)`
is the generic determinant polynomial in `A := MvPolynomial (Fin N × Fin N) k`
(issue #4736, the algebraic prerequisite of the det⁻¹-elimination kernel lemma
#4712 / #4694; route doc `progress/kernel-lemma-K-route.md`).

Neither Mathlib nor this repository has irreducibility of a generic determinant,
so we build it here.

## Reusable foundations (proven in this file)

* `irreducible_C_mul_X_add_C` — a linear polynomial `a·X + b` over an integral
  domain with `a` prime and `a ∤ b` is irreducible. This is the engine of the
  inductive determinant proof: after cofactor-expanding along column `0`, the
  generic determinant is `X(0,0)·M₀₀ + R` with `M₀₀` prime (induction
  hypothesis) and `M₀₀ ∤ R`.
* `prime_rename_of_injective` — primeness in `MvPolynomial` transfers across a
  `rename` along an injective map. This is the induction-hypothesis plumbing:
  each minor of the generic matrix is a `rename` of a smaller generic
  determinant, and `rename` along the (injective) index embedding carries
  primeness back and forth.

## Remaining work (issue successor)

The determinant-specific induction — cofactor repackaging
`detPoly = X(0,0)·M₀₀ + R`, identifying the `(0,0)`-minor as a `rename` of
`detPoly k (N-1)`, and the coprimality `M₀₀ ∤ R` — is split into a successor
issue. `detPoly_irreducible` / `detPoly_prime` are stated here with their route
documented and a single `sorry` each, so downstream code can already depend on
the statements.
-/

open MvPolynomial Polynomial

namespace Etingof.DetLocalization

variable {k : Type*} [Field k] {N : ℕ}

/-- **Linear irreducibility criterion.** Over an integral domain `B`, the degree
`1` polynomial `a·X + b` is irreducible whenever `a` is prime and `a ∤ b`.

This is the heart of the inductive proof of determinant irreducibility: viewing
the generic determinant as a polynomial in the entry `X(0,0)`, it reads
`M₀₀·X + R` with `M₀₀` prime (the `(0,0)`-minor, irreducible by induction) and
`M₀₀ ∤ R`. -/
theorem irreducible_C_mul_X_add_C {B : Type*} [CommRing B] [IsDomain B]
    {a b : B} (ha : Prime a) (hab : ¬ a ∣ b) :
    Irreducible (Polynomial.C a * Polynomial.X + Polynomial.C b) := by
  have ha0 : a ≠ 0 := ha.ne_zero
  set p : B[X] := Polynomial.C a * Polynomial.X + Polynomial.C b with hp
  have hcoeff1 : p.coeff 1 = a := by simp [hp]
  have hcoeff0 : p.coeff 0 = b := by simp [hp]
  have hpdeg : p.natDegree = 1 := by
    have hCX : (Polynomial.C a * Polynomial.X).natDegree = 1 := by
      simpa using Polynomial.natDegree_C_mul_X a ha0
    rw [hp, Polynomial.natDegree_add_C, hCX]
  have hp0 : p ≠ 0 := by
    intro h; apply ha0; rw [← hcoeff1, h]; simp
  -- The degree-`0` factor in any factorisation of `p` is a unit.
  have key : ∀ u v : B[X], p = u * v → v.natDegree = 0 → IsUnit v := by
    intro u v huv hv
    have hvC : v = Polynomial.C (v.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hv
    set c := v.coeff 0 with hc
    have hcoeffu1 : a = u.coeff 1 * c := by
      rw [← hcoeff1, huv, hvC, Polynomial.coeff_mul_C]
    have hcoeffu0 : b = u.coeff 0 * c := by
      rw [← hcoeff0, huv, hvC, Polynomial.coeff_mul_C]
    have hcunit : IsUnit c := by
      rcases ha.irreducible.isUnit_or_isUnit hcoeffu1 with h | h
      · -- `u.coeff 1` is a unit: then `c` is associate to `a`, forcing `a ∣ b`.
        exfalso
        apply hab
        obtain ⟨w, hw⟩ := h
        have hca : Associated c a := ⟨w, by rw [hcoeffu1, hw, mul_comm]⟩
        exact (hca.symm.dvd).trans ⟨u.coeff 0, by rw [hcoeffu0, mul_comm]⟩
      · exact h
    rw [hvC]
    exact Polynomial.isUnit_C.mpr hcunit
  refine ⟨?_, ?_⟩
  · intro hpu
    have := Polynomial.natDegree_eq_zero_of_isUnit hpu
    rw [hpdeg] at this; exact one_ne_zero this
  · intro u v huv
    have hu0 : u ≠ 0 := by intro h; rw [h, zero_mul] at huv; exact hp0 huv
    have hv0 : v ≠ 0 := by intro h; rw [h, mul_zero] at huv; exact hp0 huv
    have hfac : u.natDegree + v.natDegree = 1 := by
      rw [← Polynomial.natDegree_mul hu0 hv0, ← huv, hpdeg]
    have hsplit : u.natDegree = 0 ∨ v.natDegree = 0 := by omega
    rcases hsplit with hu | hv
    · exact Or.inl (key v u (by rw [huv]; ring) hu)
    · exact Or.inr (key u v huv hv)

/-- **Primeness transfers across an injective `rename`.** For an injective
re-indexing `e : σ → τ`, `rename e p` is prime in `MvPolynomial τ k` iff `p` is
prime in `MvPolynomial σ k`.

This is the induction-hypothesis plumbing for the determinant proof: each minor
of the generic matrix is `rename e (detPoly k (N-1))` for an injective `e`
embedding the smaller index set into `Fin N × Fin N`. -/
theorem prime_rename_of_injective {σ τ : Type*} {e : σ → τ}
    (he : Function.Injective e) {p : MvPolynomial σ k} :
    Prime (rename e p) ↔ Prime p := by
  classical
  -- factor `e` through its range: `e = (↑) ∘ (Equiv.ofInjective e he)`
  have hcomp : rename e p
      = rename ((↑) : Set.range e → τ) (rename (Equiv.ofInjective e he) p) := by
    rw [rename_rename]
    rfl
  -- the remaining `rename` is a ring equivalence, so it preserves primeness
  have hrw : rename (Equiv.ofInjective e he) p
      = renameEquiv k (Equiv.ofInjective e he) p := rfl
  rw [hcomp, prime_rename_iff (Set.range e), hrw]
  exact MulEquiv.prime_iff (renameEquiv k (Equiv.ofInjective e he))

/-- **Irreducibility of the generic determinant polynomial** (for `N ≥ 1`).

Route (successor issue): induction on `N`. Cofactor-expand along column `0`
(`Matrix.det_succ_column_zero`) to write `detPoly k (N+1) = X(0,0)·M₀₀ + R`,
where `M₀₀` is the `(0,0)`-minor and `R` collects the other column-`0` terms;
both are free of the variable `X(0,0)`. The minor `M₀₀` equals
`rename ψ (detPoly k N)` for the injective `ψ : (i,j) ↦ (i.succ, j.succ)`, so it
is prime by the induction hypothesis (`prime_rename_of_injective`). The
coprimality `M₀₀ ∤ R` holds because substituting the column-`0` variables shows
`M₀₀ ∣ R → M₀₀ ∣ M₁₀` for a second minor `M₁₀`, forcing the two distinct prime
minors to be associate — impossible, as `M₁₀` involves a row-`0` variable absent
from `M₀₀`. Finally `irreducible_C_mul_X_add_C` (with `a = M₀₀`, `b = R`) gives
irreducibility through the single-variable isolation equivalence. -/
theorem detPoly_irreducible (hN : 0 < N) : Irreducible (detPoly k N) := by
  sorry

/-- **Primeness of the generic determinant polynomial** (for `N ≥ 1`): immediate
from `detPoly_irreducible` since `MvPolynomial (Fin N × Fin N) k` is a unique
factorisation monoid. -/
theorem detPoly_prime (hN : 0 < N) : Prime (detPoly k N) :=
  (UniqueFactorizationMonoid.irreducible_iff_prime).mp (detPoly_irreducible hN)

end Etingof.DetLocalization
