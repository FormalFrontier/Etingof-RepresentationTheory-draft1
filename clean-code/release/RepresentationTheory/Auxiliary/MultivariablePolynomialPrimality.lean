/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import Mathlib
import RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization

/-!
# Primality of an auxiliary multivariable polynomial

This module proves irreducibility and primality of the auxiliary determinant polynomial in
matrix-entry variables.
-/

open MvPolynomial Polynomial
open RepresentationTheory.Auxiliary.GeneralLinearCoordinateLocalization

namespace RepresentationTheory.Auxiliary.MultivariablePolynomialPrimality

variable {k : Type*} [Field k] {N : ℕ}

/-- If `a` is prime and does not divide `b` in a domain, then the polynomial
`C a * X + C b` is irreducible. -/
theorem irreducible_C_mul_X_add_C_of_prime_not_dvd
    {B : Type*} [CommRing B] [IsDomain B] {a b : B} (ha : Prime a) (hab : ¬ a ∣ b) :
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
    intro h
    apply ha0
    rw [← hcoeff1, h]
    simp
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
      · exfalso
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
    rw [hpdeg] at this
    exact one_ne_zero this
  · intro u v huv
    have hu0 : u ≠ 0 := by intro h; rw [h, zero_mul] at huv; exact hp0 huv
    have hv0 : v ≠ 0 := by intro h; rw [h, mul_zero] at huv; exact hp0 huv
    have hfac : u.natDegree + v.natDegree = 1 := by
      rw [← Polynomial.natDegree_mul hu0 hv0, ← huv, hpdeg]
    have hsplit : u.natDegree = 0 ∨ v.natDegree = 0 := by omega
    rcases hsplit with hu | hv
    · exact Or.inl (key v u (by rw [huv]; ring) hu)
    · exact Or.inr (key u v huv hv)

/-- Renaming the variables of a multivariable polynomial along an injective map preserves and
reflects primality. -/
theorem prime_rename_iff_of_injective {σ τ : Type*} {e : σ → τ}
    (he : Function.Injective e) {p : MvPolynomial σ k} :
    Prime (rename e p) ↔ Prime p := by
  classical
  have hcomp : rename e p =
      rename ((↑) : Set.range e → τ) (rename (Equiv.ofInjective e he) p) := by
    rw [rename_rename]
    rfl
  have hrw : rename (Equiv.ofInjective e he) p =
      renameEquiv k (Equiv.ofInjective e he) p := rfl
  rw [hcomp, prime_rename_iff (Set.range e), hrw]
  exact MulEquiv.prime_iff (renameEquiv k (Equiv.ofInjective e he))

private lemma degreeOf_eq_zero_iff_notMem_vars {σ R : Type*} [CommSemiring R]
    (j : σ) (p : MvPolynomial σ R) : degreeOf j p = 0 ↔ j ∉ p.vars := by
  classical
  rw [degreeOf_def, vars_def, Multiset.mem_toFinset]
  exact Multiset.count_eq_zero

private lemma minor_index_injective {n : ℕ} (i : Fin (n + 1)) :
    Function.Injective (Prod.map i.succAbove (Fin.succ : Fin n → Fin (n + 1))) :=
  (Fin.succAbove_right_injective).prodMap (Fin.succ_injective n)

private lemma minor_det_eq_rename {n : ℕ} (i : Fin (n + 1)) :
    ((Matrix.mvPolynomialX (Fin (n + 1)) (Fin (n + 1)) k).submatrix i.succAbove Fin.succ).det =
      rename (Prod.map i.succAbove (Fin.succ : Fin n → Fin (n + 1)))
        (auxiliary_matrix_polynomial k n) := by
  rw [auxiliary_matrix_polynomial, AlgHom.map_det]
  congr 1
  ext p q
  simp [Matrix.submatrix_apply, Matrix.map_apply, Matrix.mvPolynomialX_apply]

private lemma mem_vars_auxiliary_matrix_polynomial {m : ℕ} :
    ((0 : Fin (m + 1)), (0 : Fin (m + 1))) ∈
      (auxiliary_matrix_polynomial k (m + 1)).vars := by
  classical
  by_contra hv
  set g₁ : Fin (m + 1) × Fin (m + 1) → k :=
    fun p => if p.1 = p.2 then (1 : k) else 0 with hg₁
  set g₂ : Fin (m + 1) × Fin (m + 1) → k :=
    fun p => if p = ((0 : Fin (m + 1)), (0 : Fin (m + 1))) then (0 : k)
      else (if p.1 = p.2 then 1 else 0) with hg₂
  have hcongr : eval g₁ (auxiliary_matrix_polynomial k (m + 1)) =
      eval g₂ (auxiliary_matrix_polynomial k (m + 1)) := by
    apply eval₂Hom_congr' rfl _ rfl
    intro i hi _
    have hne : i ≠ ((0 : Fin (m + 1)), (0 : Fin (m + 1))) := by
      rintro rfl
      exact hv hi
    simp only [hg₁, hg₂, if_neg hne]
  have hmat₁ : (Matrix.mvPolynomialX (Fin (m + 1)) (Fin (m + 1)) k).map (eval g₁) =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) := by
    ext i j
    simp [Matrix.map_apply, Matrix.mvPolynomialX_apply, MvPolynomial.eval_X, Matrix.one_apply,
      hg₁]
  have hmat₂ : (Matrix.mvPolynomialX (Fin (m + 1)) (Fin (m + 1)) k).map (eval g₂) =
      Matrix.diagonal (fun i => if i = (0 : Fin (m + 1)) then (0 : k) else 1) := by
    ext i j
    rw [Matrix.map_apply, Matrix.mvPolynomialX_apply, MvPolynomial.eval_X,
      Matrix.diagonal_apply, hg₂]
    by_cases hij : i = j
    · subst hij
      simp [Prod.ext_iff]
    · simp [hij, Prod.ext_iff]
  have hL : eval g₁ (auxiliary_matrix_polynomial k (m + 1)) = 1 := by
    rw [auxiliary_matrix_polynomial, RingHom.map_det, RingHom.mapMatrix_apply, hmat₁,
      Matrix.det_one]
  have hR : eval g₂ (auxiliary_matrix_polynomial k (m + 1)) = 0 := by
    rw [auxiliary_matrix_polynomial, RingHom.map_det, RingHom.mapMatrix_apply, hmat₂,
      Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (m + 1))) (by simp)
  rw [hL, hR] at hcongr
  exact one_ne_zero hcongr

/-- The auxiliary polynomial in matrix-entry variables is prime when the matrix size is
positive. -/
theorem auxiliary_matrix_polynomial_prime (hN : 0 < N) :
    Prime (auxiliary_matrix_polynomial k N) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  clear hN
  induction m with
  | zero =>
    have hbase : auxiliary_matrix_polynomial k 1 = X ((0 : Fin 1), (0 : Fin 1)) := by
      rw [auxiliary_matrix_polynomial, Matrix.det_fin_one, Matrix.mvPolynomialX_apply]
    rw [hbase]
    exact MvPolynomial.X_prime
  | succ n ih =>
    classical
    set A := Matrix.mvPolynomialX (Fin (n + 2)) (Fin (n + 2)) k with hA
    set v₀ : Fin (n + 2) × Fin (n + 2) := (0, 0) with hv₀
    set M₀ : MvPolynomial (Fin (n + 2) × Fin (n + 2)) k :=
      (A.submatrix (0 : Fin (n + 2)).succAbove Fin.succ).det with hM₀
    set M₁ : MvPolynomial (Fin (n + 2) × Fin (n + 2)) k :=
      (A.submatrix (1 : Fin (n + 2)).succAbove Fin.succ).det with hM₁
    set R : MvPolynomial (Fin (n + 2) × Fin (n + 2)) k :=
      ∑ i : Fin (n + 1),
        (-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) k) ^ ((i.succ : Fin (n + 2)) : ℕ)
          * X ((i.succ : Fin (n + 2)), (0 : Fin (n + 2)))
          * (A.submatrix (i.succ).succAbove Fin.succ).det with hR
    have hf0inj := minor_index_injective (n := n + 1) (0 : Fin (n + 2))
    have hf1inj := minor_index_injective (n := n + 1) (1 : Fin (n + 2))
    have hM₀rw : M₀ =
        rename (Prod.map (0 : Fin (n + 2)).succAbove Fin.succ)
          (auxiliary_matrix_polynomial k (n + 1)) := by
      rw [hM₀, hA]
      exact minor_det_eq_rename (0 : Fin (n + 2))
    have hM₁rw : M₁ =
        rename (Prod.map (1 : Fin (n + 2)).succAbove Fin.succ)
          (auxiliary_matrix_polynomial k (n + 1)) := by
      rw [hM₁, hA]
      exact minor_det_eq_rename (1 : Fin (n + 2))
    have hPrimeM₀ : Prime M₀ := by
      rw [hM₀rw]
      exact (prime_rename_iff_of_injective hf0inj).mpr ih
    have hPrimeM₁ : Prime M₁ := by
      rw [hM₁rw]
      exact (prime_rename_iff_of_injective hf1inj).mpr ih
    have hdegM₀ : degreeOf v₀ M₀ = 0 := by
      rw [degreeOf_eq_zero_iff_notMem_vars, hM₀rw]
      intro hmem
      obtain ⟨w, _, hw⟩ := mem_vars_rename _ _ hmem
      apply Fin.succ_ne_zero w.2
      simpa [hv₀, Prod.map_snd] using congrArg Prod.snd hw
    have hdegR : degreeOf v₀ R = 0 := by
      rw [hR]
      apply Nat.le_zero.mp
      apply le_trans (degreeOf_sum_le v₀ Finset.univ
        (fun i : Fin (n + 1) => (-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) k)
          ^ ((i.succ : Fin (n + 2)) : ℕ) * X ((i.succ : Fin (n + 2)), (0 : Fin (n + 2)))
          * (A.submatrix (i.succ).succAbove Fin.succ).det))
      apply Finset.sup_le
      intro i _
      have hMi0 : degreeOf v₀ ((A.submatrix (i.succ).succAbove Fin.succ).det) = 0 := by
        rw [degreeOf_eq_zero_iff_notMem_vars, hA, minor_det_eq_rename (i.succ)]
        intro hmem
        obtain ⟨w, _, hw⟩ := mem_vars_rename _ _ hmem
        apply Fin.succ_ne_zero w.2
        simpa [hv₀, Prod.map_snd] using congrArg Prod.snd hw
      have hXne : v₀ ≠ ((i.succ : Fin (n + 2)), (0 : Fin (n + 2))) := by
        intro h
        apply Fin.succ_ne_zero i
        simpa [hv₀] using (congrArg Prod.fst h).symm
      have hXdeg : degreeOf v₀
          (X ((i.succ : Fin (n + 2)), (0 : Fin (n + 2))) :
            MvPolynomial (Fin (n + 2) × Fin (n + 2)) k) = 0 := by
        rw [degreeOf_X, if_neg hXne]
      have hsign : ((-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) k)
          ^ ((i.succ : Fin (n + 2)) : ℕ)) =
          MvPolynomial.C ((-1 : k) ^ ((i.succ : Fin (n + 2)) : ℕ)) := by
        rw [map_pow, map_neg, map_one]
      have hXterm : degreeOf v₀
          ((-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) k)
            ^ ((i.succ : Fin (n + 2)) : ℕ) *
              X ((i.succ : Fin (n + 2)), (0 : Fin (n + 2)))) = 0 := by
        rw [hsign]
        exact Nat.le_zero.mp ((degreeOf_C_mul_le _ _ _).trans hXdeg.le)
      calc
        degreeOf v₀ ((-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) k)
              ^ ((i.succ : Fin (n + 2)) : ℕ) * X ((i.succ : Fin (n + 2)), (0 : Fin (n + 2)))
              * (A.submatrix (i.succ).succAbove Fin.succ).det) ≤
            degreeOf v₀ ((-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) k)
                ^ ((i.succ : Fin (n + 2)) : ℕ) *
                  X ((i.succ : Fin (n + 2)), (0 : Fin (n + 2)))) +
              degreeOf v₀ ((A.submatrix (i.succ).succAbove Fin.succ).det) :=
          degreeOf_mul_le _ _ _
        _ = 0 := by rw [hXterm, hMi0]
    have hcop : ¬ (M₀ ∣ R) := by
      intro hdvd
      set g : Fin (n + 2) × Fin (n + 2) → MvPolynomial (Fin (n + 2) × Fin (n + 2)) k :=
        fun v => if v.2 = 0 then (if v.1 = 1 then 1 else 0) else X v with hg
      have hev_minor : ∀ j : Fin (n + 2),
          aeval g (rename (Prod.map j.succAbove (Fin.succ : Fin (n + 1) → Fin (n + 2)))
              (auxiliary_matrix_polynomial k (n + 1))) =
            rename (Prod.map j.succAbove Fin.succ)
              (auxiliary_matrix_polynomial k (n + 1)) := by
        intro j
        rw [aeval_rename]
        have hcomp :
            (g ∘ Prod.map j.succAbove (Fin.succ : Fin (n + 1) → Fin (n + 2))) =
              ((X : (Fin (n + 2) × Fin (n + 2)) → _) ∘ Prod.map j.succAbove Fin.succ) := by
          funext pq
          simp only [Function.comp_apply, hg, Prod.map_snd]
          rw [if_neg (Fin.succ_ne_zero pq.2)]
        rw [hcomp, ← aeval_rename, MvPolynomial.aeval_X_left_apply]
      have hevM₀ : aeval g M₀ = M₀ := by rw [hM₀rw]; exact hev_minor 0
      have hg10 : g ((1 : Fin (n + 2)), (0 : Fin (n + 2))) = 1 := by simp [hg]
      have hmin : aeval g ((A.submatrix (1 : Fin (n + 2)).succAbove Fin.succ).det) = M₁ := by
        conv_rhs => rw [hM₁rw]
        rw [hA, minor_det_eq_rename (1 : Fin (n + 2))]
        exact hev_minor (1 : Fin (n + 2))
      have hevR : aeval g R = -M₁ := by
        rw [hR, map_sum, Finset.sum_eq_single (0 : Fin (n + 1))]
        · rw [Fin.succ_zero_eq_one', map_mul, map_mul, map_pow, map_neg, map_one,
            MvPolynomial.aeval_X, hg10, hmin]
          simp
        · intro i _ hi0
          rw [map_mul, map_mul, MvPolynomial.aeval_X]
          have hne1 : (i.succ : Fin (n + 2)) ≠ 1 := by
            intro h
            apply hi0
            apply Fin.succ_injective
            rw [h, Fin.succ_zero_eq_one']
          rw [show g ((i.succ : Fin (n + 2)), (0 : Fin (n + 2))) = 0 by
            simp [hg, hne1]]
          ring
        · intro h
          exact absurd (Finset.mem_univ _) h
      have hdvd2 : M₀ ∣ M₁ := by
        have hh := map_dvd (MvPolynomial.aeval g) hdvd
        rw [hevM₀, hevR] at hh
        exact dvd_neg.mp hh
      obtain ⟨u, hu⟩ := hPrimeM₀.associated_of_dvd hPrimeM₁ hdvd2
      obtain ⟨c₀, hc₀unit, hc₀eq⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).mp u.isUnit
      have hM₁eq : M₁ = MvPolynomial.C c₀ * M₀ := by rw [← hu, hc₀eq, mul_comm]
      set w₁ : Fin (n + 2) × Fin (n + 2) := (0, 1) with hw₁
      have hdegM₁pos : degreeOf w₁ M₁ ≠ 0 := by
        rw [hM₁rw]
        have hf1 : Prod.map (1 : Fin (n + 2)).succAbove
            (Fin.succ : Fin (n + 1) → Fin (n + 2)) (0, 0) = w₁ := by
          simp [Prod.map, hw₁]
        rw [← hf1, degreeOf_rename_of_injective hf1inj, Ne,
          degreeOf_eq_zero_iff_notMem_vars, not_not]
        exact mem_vars_auxiliary_matrix_polynomial (m := n)
      have hdegM₁zero : degreeOf w₁ M₁ = 0 := by
        rw [hM₁eq, degreeOf_C_mul w₁ c₀ (mem_nonZeroDivisors_of_ne_zero hc₀unit.ne_zero),
          degreeOf_eq_zero_iff_notMem_vars, hM₀rw]
        intro hmem
        obtain ⟨z, _, hz⟩ := mem_vars_rename _ _ hmem
        apply Fin.succ_ne_zero z.1
        simpa [hw₁, Prod.map_fst, Fin.succAbove_zero] using congrArg Prod.fst hz
      exact hdegM₁pos hdegM₁zero
    set Φ : MvPolynomial (Fin (n + 2) × Fin (n + 2)) k ≃ₐ[k]
        Polynomial (MvPolynomial {v : Fin (n + 2) × Fin (n + 2) // v ≠ v₀} k) :=
      (renameEquiv k (Equiv.optionSubtypeNe v₀).symm).trans (optionEquivLeft k _) with hΦ
    have hΦeq : ∀ p : MvPolynomial (Fin (n + 2) × Fin (n + 2)) k,
        Φ p = optionEquivLeft k _ (rename (Equiv.optionSubtypeNe v₀).symm p) := by
      intro p
      simp only [hΦ, AlgEquiv.trans_apply, renameEquiv_apply]
    have hΦX : Φ (X v₀) = Polynomial.X := by
      rw [hΦeq, rename_X, Equiv.optionSubtypeNe_symm_self, optionEquivLeft_X_none]
    have hnatM₀ : (Φ M₀).natDegree = 0 := by
      rw [hΦeq, ← degreeOf_eq_natDegree]
      exact hdegM₀
    have hnatR : (Φ R).natDegree = 0 := by
      rw [hΦeq, ← degreeOf_eq_natDegree]
      exact hdegR
    set a₀ := (Φ M₀).coeff 0 with ha₀
    set b₀ := (Φ R).coeff 0 with hb₀
    have hΦM₀ : Φ M₀ = Polynomial.C a₀ :=
      Polynomial.eq_C_of_natDegree_eq_zero hnatM₀
    have hΦR : Φ R = Polynomial.C b₀ := Polynomial.eq_C_of_natDegree_eq_zero hnatR
    have hdecomp : auxiliary_matrix_polynomial k (n + 2) = X v₀ * M₀ + R := by
      rw [auxiliary_matrix_polynomial, Matrix.det_succ_column_zero, Fin.sum_univ_succ, hM₀, hR,
        hA, hv₀]
      simp only [Matrix.mvPolynomialX_apply, Fin.val_zero, pow_zero, one_mul]
    have hΦdet : Φ (auxiliary_matrix_polynomial k (n + 2)) =
        Polynomial.C a₀ * Polynomial.X + Polynomial.C b₀ := by
      rw [hdecomp, map_add, map_mul, hΦX, hΦM₀, hΦR]
      ring
    have ha₀prime : Prime a₀ := by
      rw [← Polynomial.prime_C_iff, ← hΦM₀]
      exact (MulEquiv.prime_iff Φ.toMulEquiv).mpr hPrimeM₀
    have hndvd : ¬ a₀ ∣ b₀ := by
      intro h
      apply hcop
      have hdC : Φ M₀ ∣ Φ R := by
        rw [hΦM₀, hΦR]
        exact map_dvd Polynomial.C h
      have hback := map_dvd Φ.symm hdC
      simpa using hback
    have hirr : Irreducible (auxiliary_matrix_polynomial k (n + 2)) := by
      have hlin := irreducible_C_mul_X_add_C_of_prime_not_dvd ha₀prime hndvd
      rw [← hΦdet] at hlin
      exact (MulEquiv.irreducible_iff Φ.toMulEquiv).mp hlin
    exact (UniqueFactorizationMonoid.irreducible_iff_prime).mp hirr

/-- The auxiliary polynomial in matrix-entry variables is irreducible when the matrix size is
positive. -/
theorem auxiliary_matrix_polynomial_irreducible (hN : 0 < N) :
    Irreducible (auxiliary_matrix_polynomial k N) :=
  (auxiliary_matrix_polynomial_prime hN).irreducible

end RepresentationTheory.Auxiliary.MultivariablePolynomialPrimality
