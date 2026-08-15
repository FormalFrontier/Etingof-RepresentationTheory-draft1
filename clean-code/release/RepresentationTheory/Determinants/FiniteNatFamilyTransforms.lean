/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import RepresentationTheory.MvPolynomial.UniformIndexShift

set_option linter.style.longLine false

noncomputable section

namespace RepresentationTheory.Determinants.FiniteNatFamilyTransforms

open MvPolynomial

/-- Transforms a natural-number-valued family indexed by Fin N using a natural-number parameter. -/
def finiteNatFamilyTransform (N : ℕ) (lam : Fin N → ℕ) (s : ℕ) : Fin N → ℕ :=
  fun j => s - lam (Fin.rev j)

/-- Shows that applying the finite-family transformation at any parameter preserves antitonicity. -/
theorem finiteNatFamilyTransform_antitone (N : ℕ) (lam : Fin N → ℕ)
    (hlam : Antitone lam) (s : ℕ) : Antitone (finiteNatFamilyTransform N lam s) := by
  intro i j hij
  have h := hlam (Fin.rev_anti hij)
  simp only [finiteNatFamilyTransform]
  omega

private theorem complementExps_eq (N : ℕ) (lam : Fin N → ℕ) (s : ℕ)
    (hs : ∀ j, lam j ≤ s) :
    (fun j => (s + N - 1) -
      RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam j) =
      fun j =>
        RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N
          (finiteNatFamilyTransform N lam s) (Fin.rev j) := by
  funext j
  have hj := hs j
  have hjlt := j.isLt
  simp only [RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase,
    finiteNatFamilyTransform, Fin.rev_rev, Fin.val_rev]
  omega

/-- For a finite natural-number family bounded by the parameter, relates a determinant of an associated subtraction matrix to the reversal sign, a factor derived from the transformed family, and another determinant. -/
theorem det_eq_reversePermSign_mul (N : ℕ) (lam : Fin N → ℕ) (s : ℕ)
    (hs : ∀ j, lam j ≤ s) :
    (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N
      (fun j => (s + N - 1) -
        RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N lam j)).det =
      (↑↑(Fin.revPerm (n := N)).sign : MvPolynomial (Fin N) ℚ) *
        (RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial N
          (finiteNatFamilyTransform N lam s) *
          (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N
            (RepresentationTheory.SymmetricPolynomials.Alternant.staircaseExponents N)).det) := by
  rw [complementExps_eq N lam s hs]
  have hmat :
      RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N
          (fun j =>
            RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N
              (finiteNatFamilyTransform N lam s) (Fin.rev j)) =
        (RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix N
          (RepresentationTheory.SymmetricPolynomials.Alternant.addStaircase N
            (finiteNatFamilyTransform N lam s))).submatrix id Fin.revPerm := by
    ext i j
    simp only [RepresentationTheory.SymmetricPolynomials.Alternant.alternantMatrix,
      Matrix.of_apply, Matrix.submatrix_apply, id_eq, Fin.revPerm_apply]
  rw [hmat, Matrix.det_permute',
    RepresentationTheory.SymmetricPolynomials.Alternant.partitionPolynomial_mul_det_staircase]

end RepresentationTheory.Determinants.FiniteNatFamilyTransforms
