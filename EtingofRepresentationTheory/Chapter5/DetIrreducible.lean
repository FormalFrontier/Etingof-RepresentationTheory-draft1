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

/-- A variable does not occur in a polynomial exactly when its `degreeOf` is `0`. -/
private lemma degreeOf_eq_zero_iff_notMem_vars {σ R : Type*} [CommSemiring R]
    (j : σ) (p : MvPolynomial σ R) : degreeOf j p = 0 ↔ j ∉ p.vars := by
  classical
  rw [degreeOf_def, vars_def, Multiset.mem_toFinset]
  exact Multiset.count_eq_zero

/-- The index map carving out the `(i,·)`-minor of the generic `(n+1)×(n+1)`
matrix: `(p,q) ↦ (i.succAbove p, q.succ)`. It is injective. -/
private lemma minor_index_injective {n : ℕ} (i : Fin (n + 1)) :
    Function.Injective (Prod.map i.succAbove (Fin.succ : Fin n → Fin (n + 1))) :=
  (Fin.succAbove_right_injective).prodMap (Fin.succ_injective n)

/-- The `(i,0)`-cofactor minor of the generic determinant is a `rename` of the
generic determinant one size down. -/
private lemma minor_det_eq_rename {n : ℕ} (i : Fin (n + 1)) :
    ((Matrix.mvPolynomialX (Fin (n + 1)) (Fin (n + 1)) k).submatrix i.succAbove Fin.succ).det
      = rename (Prod.map i.succAbove (Fin.succ : Fin n → Fin (n + 1))) (detPoly k n) := by
  rw [detPoly, AlgHom.map_det]
  congr 1
  ext p q
  simp [Matrix.submatrix_apply, Matrix.map_apply, Matrix.mvPolynomialX_apply]

/-- The variable `X(0,0)` occurs in the generic determinant polynomial (for
`m ≥ 1`): the determinant genuinely depends on the top-left entry, witnessed by
evaluating at the identity matrix versus the identity with the `(0,0)` entry
zeroed (det `1` versus `0`). -/
private lemma mem_vars_detPoly {m : ℕ} :
    ((0 : Fin (m + 1)), (0 : Fin (m + 1))) ∈ (detPoly k (m + 1)).vars := by
  classical
  by_contra hv
  set g₁ : Fin (m + 1) × Fin (m + 1) → k := fun p => if p.1 = p.2 then (1 : k) else 0 with hg₁
  set g₂ : Fin (m + 1) × Fin (m + 1) → k :=
    fun p => if p = ((0 : Fin (m + 1)), (0 : Fin (m + 1))) then (0 : k)
      else (if p.1 = p.2 then 1 else 0) with hg₂
  have hcongr : eval g₁ (detPoly k (m + 1)) = eval g₂ (detPoly k (m + 1)) := by
    apply eval₂Hom_congr' rfl _ rfl
    intro i hi _
    have hne : i ≠ ((0 : Fin (m + 1)), (0 : Fin (m + 1))) := by rintro rfl; exact hv hi
    simp only [hg₁, hg₂, if_neg hne]
  have hmat₁ : (Matrix.mvPolynomialX (Fin (m + 1)) (Fin (m + 1)) k).map (eval g₁)
      = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) := by
    ext i j
    simp [Matrix.map_apply, Matrix.mvPolynomialX_apply, MvPolynomial.eval_X, Matrix.one_apply, hg₁]
  have hmat₂ : (Matrix.mvPolynomialX (Fin (m + 1)) (Fin (m + 1)) k).map (eval g₂)
      = Matrix.diagonal (fun i => if i = (0 : Fin (m + 1)) then (0 : k) else 1) := by
    ext i j
    rw [Matrix.map_apply, Matrix.mvPolynomialX_apply, MvPolynomial.eval_X, Matrix.diagonal_apply, hg₂]
    by_cases hij : i = j
    · subst hij; simp [Prod.ext_iff]
    · simp [hij, Prod.ext_iff]
  have hL : eval g₁ (detPoly k (m + 1)) = 1 := by
    rw [detPoly, RingHom.map_det, RingHom.mapMatrix_apply, hmat₁, Matrix.det_one]
  have hR : eval g₂ (detPoly k (m + 1)) = 0 := by
    rw [detPoly, RingHom.map_det, RingHom.mapMatrix_apply, hmat₂, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (m + 1))) (by simp)
  rw [hL, hR] at hcongr
  exact one_ne_zero hcongr

/-- **Primeness of the generic determinant polynomial** (for `N ≥ 1`). -/
theorem detPoly_prime (hN : 0 < N) : Prime (detPoly k N) := by
  sorry

/-- **Irreducibility of the generic determinant polynomial** (for `N ≥ 1`):
immediate from `detPoly_prime`. -/
theorem detPoly_irreducible (hN : 0 < N) : Irreducible (detPoly k N) :=
  (detPoly_prime hN).irreducible

end Etingof.DetLocalization
