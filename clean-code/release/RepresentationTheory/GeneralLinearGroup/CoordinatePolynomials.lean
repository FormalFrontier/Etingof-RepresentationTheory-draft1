/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/

import RepresentationTheory.GeneralLinearGroup.DiagonalAction

open MvPolynomial

noncomputable section

namespace RepresentationTheory.GeneralLinearGroup.CoordinatePolynomials

/-- The multivariable polynomial in matrix entries representing the determinant. -/
def determinantPolynomial (k : Type*) [Field k] (N : ℕ) :
    MvPolynomial (Fin N × Fin N) k :=
  (Matrix.of fun i j : Fin N => MvPolynomial.X (i, j)).det

/-- Evaluating the determinant polynomial at an invertible matrix gives its determinant. -/
@[simp]
theorem eval_determinantPolynomial {k : Type*} [Field k] {N : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin N) k) :
    MvPolynomial.eval
        (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
        (determinantPolynomial k N) = (g : Matrix (Fin N) (Fin N) k).det := by
  unfold determinantPolynomial
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.map_apply]

/-- An equivalence between the extended coordinate index type and an optional pair of matrix indices. -/
def coordinateIndexEquiv (N : ℕ) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex N ≃
      Option (Fin N × Fin N) where
  toFun := Sum.elim some fun _ => none
  invFun := fun o => o.elim (Sum.inr ()) Sum.inl
  left_inv := by rintro (ij | ⟨⟩) <;> rfl
  right_inv := by rintro (_ | ij) <;> rfl

/-- The algebra equivalence identifying polynomials in extended coordinates with univariate polynomials over matrix-entry polynomials. -/
def coordinatePolynomialEquiv (k : Type*) [Field k] (N : ℕ) :
    MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex N) k ≃ₐ[k]
      Polynomial (MvPolynomial (Fin N × Fin N) k) :=
  (MvPolynomial.renameEquiv k (coordinateIndexEquiv N)).trans
    (MvPolynomial.optionEquivLeft k (Fin N × Fin N))

/-- Evaluation after the coordinate polynomial equivalence agrees with substituting matrix entries and the inverse determinant. -/
theorem evaluate_coordinatePolynomialEquiv {k : Type*} [Field k] {N : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin N) k)
    (p : MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex N) k) :
    RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g p =
      Polynomial.eval₂
        (MvPolynomial.eval fun ij : Fin N × Fin N =>
          (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
        ((g : Matrix (Fin N) (Fin N) k).det)⁻¹
        (coordinatePolynomialEquiv k N p) := by
  have hring :
      (MvPolynomial.eval (Sum.elim
          (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
          (fun _ => ((g : Matrix (Fin N) (Fin N) k).det)⁻¹)) :
        MvPolynomial (RepresentationTheory.GeneralLinearGroup.Auxiliary.AuxiliaryIndex N) k →+* k) =
        (Polynomial.eval₂RingHom
          (MvPolynomial.eval fun ij : Fin N × Fin N =>
            (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
          ((g : Matrix (Fin N) (Fin N) k).det)⁻¹).comp
          (coordinatePolynomialEquiv k N).toAlgHom.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [coordinatePolynomialEquiv, coordinateIndexEquiv]
    · intro v
      rcases v with ij | u
      · simp [coordinatePolynomialEquiv, coordinateIndexEquiv]
      · simp [coordinatePolynomialEquiv, coordinateIndexEquiv]
  have := RingHom.congr_fun hring p
  simpa [RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation]
    using this

/-- Clears an inverse-determinant denominator in a polynomial expression at a specified natural degree. -/
def clearDeterminantDenominator (k : Type*) [Field k] (N : ℕ)
    (q : Polynomial (MvPolynomial (Fin N × Fin N) k)) (s : ℕ) :
    MvPolynomial (Fin N × Fin N) k :=
  ∑ j ∈ Finset.range (s + 1), q.coeff j * determinantPolynomial k N ^ (s - j)

/-- Evaluating a denominator-cleared polynomial gives a determinant power times evaluation with the inverse determinant substituted. -/
theorem eval_clearDeterminantDenominator {k : Type*} [Field k] {N : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin N) k)
    (q : Polynomial (MvPolynomial (Fin N × Fin N) k)) (s : ℕ)
    (hq : q.natDegree ≤ s) :
    MvPolynomial.eval
        (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
        (clearDeterminantDenominator k N q s) =
      (g : Matrix (Fin N) (Fin N) k).det ^ s *
        Polynomial.eval₂
          (MvPolynomial.eval fun ij : Fin N × Fin N =>
            (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
          ((g : Matrix (Fin N) (Fin N) k).det)⁻¹ q := by
  have hD : (g : Matrix (Fin N) (Fin N) k).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det g).ne_zero
  unfold clearDeterminantDenominator
  rw [map_sum, Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hq) _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hj
  rw [map_mul, map_pow, eval_determinantPolynomial]
  have key : ∀ A D : k, D ≠ 0 → A * D ^ (s - j) = D ^ s * (A * D⁻¹ ^ j) := by
    intro A D hD'
    rw [pow_sub₀ D hD' hj, inv_pow, mul_left_comm]
  exact key _ _ hD

/-- There is a determinant power such that twisting the given general-linear-group action by that power satisfies the target predicate. -/
theorem _root_.RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty.exists_det_twist
    {k : Type*} [Field k] {N : ℕ}
    {Y : Type*} [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    {ρ : Matrix.GeneralLinearGroup (Fin N) k → Y →ₗ[k] Y}
    (h : RepresentationTheory.GeneralLinearGroup.Auxiliary.HasAuxiliaryMapProperty N ρ) :
    ∃ s : ℕ, RepresentationTheory.GeneralLinearGroup.DiagonalAction.IsAuxiliaryEndomorphismFamily N
      (fun g => ((Matrix.GeneralLinearGroup.det g : k) ^ s) • ρ g) := by
  classical
  obtain ⟨m, b, P, hP⟩ := h
  set s := Finset.univ.sup
    (fun a : Fin m => Finset.univ.sup
      (fun c : Fin m => (coordinatePolynomialEquiv k N (P a c)).natDegree)) with hs_def
  refine ⟨s, m, b, fun a c =>
    clearDeterminantDenominator k N (coordinatePolynomialEquiv k N (P a c)) s,
    fun g a c => ?_⟩
  have hdeg : (coordinatePolynomialEquiv k N (P a c)).natDegree ≤ s := by
    rw [hs_def]
    refine le_trans
      (Finset.le_sup
        (f := fun c : Fin m => (coordinatePolynomialEquiv k N (P a c)).natDegree)
        (Finset.mem_univ c))
      (Finset.le_sup (f := fun a : Fin m => Finset.univ.sup
        (fun c : Fin m => (coordinatePolynomialEquiv k N (P a c)).natDegree))
        (Finset.mem_univ a))
  have hdk : (Matrix.GeneralLinearGroup.det g : k) =
      (g : Matrix (Fin N) (Fin N) k).det :=
    Matrix.GeneralLinearGroup.val_det_apply g
  have e1 : b.repr (((Matrix.GeneralLinearGroup.det g : k) ^ s • ρ g) (b c)) a =
      (Matrix.GeneralLinearGroup.det g : k) ^ s *
        RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g
          (P a c) := by
    rw [LinearMap.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul, hP g a c]
  have e3 := eval_clearDeterminantDenominator g
    (coordinatePolynomialEquiv k N (P a c)) s hdeg
  have hAB : (Matrix.GeneralLinearGroup.det g : k) ^ s *
        RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g
          (P a c) =
      (g : Matrix (Fin N) (Fin N) k).det ^ s *
        Polynomial.eval₂
          (MvPolynomial.eval fun ij : Fin N × Fin N =>
            (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2)
          ((g : Matrix (Fin N) (Fin N) k).det)⁻¹
          (coordinatePolynomialEquiv k N (P a c)) :=
    (congrArg
      (fun t : k => t ^ s *
        RepresentationTheory.GeneralLinearGroup.Auxiliary.auxiliaryPolynomialEvaluation g
          (P a c)) hdk).trans
      (congrArg
        (fun u : k => (g : Matrix (Fin N) (Fin N) k).det ^ s * u)
        (evaluate_coordinatePolynomialEquiv g (P a c)))
  exact e1.trans (hAB.trans e3.symm)

end RepresentationTheory.GeneralLinearGroup.CoordinatePolynomials
