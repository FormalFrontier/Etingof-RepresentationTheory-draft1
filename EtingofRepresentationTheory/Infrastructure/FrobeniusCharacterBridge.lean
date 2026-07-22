import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1
import EtingofRepresentationTheory.Chapter5.Theorem5_15_1
import EtingofRepresentationTheory.Infrastructure.YoungSymTraceKronecker

/-!
# Frobenius Character Bridge

Bridge infrastructure between `charValue` (polynomial coefficient definition over ℚ
with N variables) and `spechtModuleCharacter` (trace definition over ℂ with n variables).

## Key results

* `alternantDet_eq_sign_mul_vandermondeProd` — exact alternant-Vandermonde identity
* `charValue_cast_complex` — cast `charValue` from ℚ to ℂ

## Note

The main theorem `youngSym_charValue_orthogonality` is proved in
`Theorem5_22_1.lean` using an inlined version of the trace Kronecker identity.
Two sorry'd bridge lemmas remain:
- `charValue_eq_spechtModuleCharacter`: Frobenius character formula for N variables
- `weightToPartition_eq_iff`: antitone partition injectivity
-/

noncomputable section

namespace Etingof

open MvPolynomial Finset

/-! ### Exact alternant-vandermonde identity -/

/-- The alternant determinant with Vandermonde exponents equals `sign(revPerm)` times the
Vandermonde product `∏_{i<j}(X_j - X_i)` as MvPolynomial over ℚ. -/
theorem alternantDet_eq_sign_mul_vandermondeProd (N : ℕ) :
    (alternantMatrix N (vandermondeExps N)).det =
      ((Equiv.Perm.sign (@Fin.revPerm N) : ℤ) : MvPolynomial (Fin N) ℚ) *
        ∏ i : Fin N, ∏ j ∈ Ioi i,
          (MvPolynomial.X j - MvPolynomial.X i : MvPolynomial (Fin N) ℚ) := by
  have h1 : alternantMatrix N (vandermondeExps N) =
      (Matrix.vandermonde (MvPolynomial.X : Fin N → MvPolynomial (Fin N) ℚ)).submatrix
        id (@Fin.revPerm N) := by
    ext i j
    simp only [alternantMatrix, Matrix.vandermonde, vandermondeExps, Matrix.of_apply,
      Matrix.submatrix_apply, id, Fin.revPerm_apply]
    congr 2
    simp only [Fin.rev, Fin.val_mk]
    omega
  rw [h1, Matrix.det_permute', Matrix.det_vandermonde]

/-! ### Base change: ℚ → ℂ for polynomial coefficients -/

/-- Cast `charValue` from ℚ to ℂ: it equals the coefficient in the ℂ-polynomial. -/
theorem charValue_cast_complex (N n : ℕ) (lam : BoundedPartition N n)
    (μ : Nat.Partition n) :
    (charValue N lam μ : ℂ) =
      MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm (shiftedExps N lam.parts))
        (MvPolynomial.map (algebraMap ℚ ℂ) ((alternantMatrix N (vandermondeExps N)).det *
          MvPolynomial.psumPart (Fin N) ℚ μ)) := by
  rw [MvPolynomial.coeff_map]; rfl

end Etingof
