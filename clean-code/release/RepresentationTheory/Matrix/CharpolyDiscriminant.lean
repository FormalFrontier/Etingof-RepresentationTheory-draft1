/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
import Mathlib

/-!
# Characteristic-polynomial discriminants

This module organizes discriminant constructions and their supporting polynomial lemmas.
-/

namespace RepresentationTheory.Matrix.CharpolyDiscriminant

open _root_.Matrix
open Polynomial

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A ring homomorphism carries the discriminant of a monic polynomial to the discriminant of its image. -/
theorem discr_map_of_monic [Nontrivial S] {f : R[X]} (hf : f.Monic) (φ : R →+* S) :
    (f.map φ).discr = φ f.discr := by
  rcases Nat.eq_zero_or_pos f.natDegree with h0 | hpos
  · obtain rfl := eq_one_of_monic_natDegree_zero hf h0
    rw [Polynomial.map_one, show (1 : S[X]).discr = 1 from by rw [← C_1, discr_C],
      show (1 : R[X]).discr = 1 from by rw [← C_1, discr_C], map_one]
  · have hmap_monic : (f.map φ).Monic := hf.map φ
    have hnd : (f.map φ).natDegree = f.natDegree := hf.natDegree_map φ
    have hdeg : 0 < f.degree := natDegree_pos_iff_degree_pos.mp hpos
    have hdeg' : 0 < (f.map φ).degree := natDegree_pos_iff_degree_pos.mp (hnd ▸ hpos)
    have e1 := resultant_deriv (f := f) hdeg
    rw [hf.leadingCoeff, mul_one] at e1
    have e2 := resultant_deriv (f := f.map φ) hdeg'
    rw [hmap_monic.leadingCoeff, mul_one, derivative_map, hnd, resultant_map_map, e1] at e2
    rw [map_mul, map_pow, map_neg, map_one] at e2
    have hu : IsUnit ((-1 : S) ^ (f.natDegree * (f.natDegree - 1) / 2)) :=
      (isUnit_one.neg).pow _
    exact ((hu.mul_right_inj).mp e2).symm

/-- Under the stated derivative-degree condition, a polynomial is separable exactly when its discriminant is nonzero. -/
theorem discr_ne_zero_iff_separable_of_natDegree_derivative_eq {K : Type*} [Field K] {f : K[X]}
    (hpos : 0 < f.natDegree) (hd : f.derivative.natDegree = f.natDegree - 1) :
    f.discr ≠ 0 ↔ f.Separable := by
  have hf0 : f ≠ 0 := fun h => by simp [h] at hpos
  have hdeg : 0 < f.degree := natDegree_pos_iff_degree_pos.mp hpos
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  have hres := resultant_deriv (f := f) hdeg
  have hunit : ((-1 : K)) ^ (f.natDegree * (f.natDegree - 1) / 2) ≠ 0 :=
    pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hreseq : resultant f f.derivative
      = resultant f f.derivative f.natDegree (f.natDegree - 1) := by rw [hd]
  constructor
  · intro hdiscr
    have hne : resultant f f.derivative ≠ 0 := by
      rw [hreseq, hres]
      exact mul_ne_zero (mul_ne_zero hunit hlc) hdiscr
    rw [separable_def]
    by_contra hcop
    exact hne (resultant_eq_zero_iff.mpr ⟨Or.inl hf0, hcop⟩)
  · intro hsep
    have hcop : IsCoprime f (derivative f) := (separable_def f).mp hsep
    have hne : resultant f f.derivative ≠ 0 := resultant_ne_zero f f.derivative hcop
    rw [hreseq, hres] at hne
    intro hd0
    exact hne (by rw [hd0, mul_zero])

end Polynomial

open Polynomial MvPolynomial

variable {N : ℕ} {k : Type*} [Field k]

/-- A characteristic polynomial with nonvanishing discriminant is separable. -/
theorem charpoly_separable_of_discr_ne_zero [CharZero k] (M : Matrix (Fin N) (Fin N) k)
    (hN : 0 < N) (h : M.discr ≠ 0) : M.charpoly.Separable := by
  have hpos : 0 < M.charpoly.natDegree := by
    rw [M.charpoly_natDegree_eq_dim]; simpa using hN
  have hd : M.charpoly.derivative.natDegree = M.charpoly.natDegree - 1 :=
    natDegree_eq_of_degree_eq_some (degree_derivative_eq _ hpos)
  exact (Polynomial.discr_ne_zero_iff_separable_of_natDegree_derivative_eq hpos hd).mp h

/-- The roots of a characteristic polynomial have no repetitions when its discriminant is nonzero. -/
theorem charpoly_roots_nodup_of_discr_ne_zero [CharZero k] (M : Matrix (Fin N) (Fin N) k)
    (hN : 0 < N) (h : M.discr ≠ 0) : M.charpoly.roots.Nodup :=
  Polynomial.nodup_roots (charpoly_separable_of_discr_ne_zero M hN h)

/-- A nonzero characteristic-polynomial discriminant gives exactly one distinct root for each matrix dimension. -/
theorem charpoly_rootFinset_card_eq_of_discr_ne_zero [IsAlgClosed k] [CharZero k] [DecidableEq k]
    (M : Matrix (Fin N) (Fin N) k)
    (hN : 0 < N) (h : M.discr ≠ 0) : M.charpoly.roots.toFinset.card = N := by
  rw [Multiset.toFinset_card_of_nodup (charpoly_roots_nodup_of_discr_ne_zero M hN h),
    ← (IsAlgClosed.splits M.charpoly).natDegree_eq_card_roots, M.charpoly_natDegree_eq_dim,
    Fintype.card_fin]

/-- The discriminant polynomial of a square matrix of independent variables. -/
noncomputable def genericMatrixDiscriminant
    (k : Type*) [Field k] (N : ℕ) : MvPolynomial (Fin N × Fin N) k :=
  (mvPolynomialX (Fin N) (Fin N) k).discr

/-- Evaluating the generic matrix discriminant gives the discriminant of the resulting matrix. -/
theorem eval_genericMatrixDiscriminant (N : ℕ) (x : Fin N × Fin N → k) :
    MvPolynomial.eval x (genericMatrixDiscriminant k N) =
      (Matrix.of fun i j => x (i, j)).discr := by
  set M : Matrix (Fin N) (Fin N) k := Matrix.of fun i j => x (i, j) with hM
  have hMmap : (mvPolynomialX (Fin N) (Fin N) k).map (MvPolynomial.eval x) = M := by
    ext i j
    simp only [Matrix.map_apply, mvPolynomialX_apply, MvPolynomial.eval_X, hM, Matrix.of_apply]
  have hchar : M.charpoly
      = (mvPolynomialX (Fin N) (Fin N) k).charpoly.map (MvPolynomial.eval x) := by
    rw [← hMmap, charpoly_map]
  rw [genericMatrixDiscriminant]
  simp only [Matrix.discr]
  rw [hchar, Polynomial.discr_map_of_monic (charpoly_monic _) (MvPolynomial.eval x)]

/-- The generic matrix discriminant polynomial is nonzero in positive size over characteristic zero. -/
theorem genericMatrixDiscriminant_ne_zero [CharZero k]
    (N : ℕ) (hN : 0 < N) : genericMatrixDiscriminant k N ≠ 0 := by
  intro hzero
  set d : Fin N → k := fun i => (i.val : k) with hd
  set x : Fin N × Fin N → k := fun p => if p.1 = p.2 then d p.1 else 0 with hx
  have hM : (Matrix.of fun i j => x (i, j)) = Matrix.diagonal d := by
    ext i j; simp [hx, Matrix.diagonal_apply, Matrix.of_apply]
  have heval : MvPolynomial.eval x (genericMatrixDiscriminant k N) =
      (Matrix.diagonal d).discr := by
    rw [eval_genericMatrixDiscriminant, hM]
  rw [hzero, map_zero] at heval
  have hinj : Function.Injective d := by
    intro a b hab
    apply Fin.val_injective
    have : (a.val : k) = (b.val : k) := hab
    exact_mod_cast this
  have hsep : (Matrix.diagonal d).charpoly.Separable := by
    rw [charpoly_diagonal]
    exact separable_prod_X_sub_C_iff.mpr hinj
  have hpos : 0 < (Matrix.diagonal d).charpoly.natDegree := by
    rw [charpoly_natDegree_eq_dim]; simpa using hN
  have hdd : (Matrix.diagonal d).charpoly.derivative.natDegree
      = (Matrix.diagonal d).charpoly.natDegree - 1 :=
    natDegree_eq_of_degree_eq_some (degree_derivative_eq _ hpos)
  have hdisc : (Matrix.diagonal d).discr ≠ 0 := by
    rw [Matrix.discr]
    exact
      (Polynomial.discr_ne_zero_iff_separable_of_natDegree_derivative_eq hpos hdd).mpr hsep
  exact hdisc heval.symm

end RepresentationTheory.Matrix.CharpolyDiscriminant
