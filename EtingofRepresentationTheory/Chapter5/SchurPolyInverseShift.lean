import EtingofRepresentationTheory.Chapter5.SchurPolyShift

/-!
# The inverted-variable Schur identity `s_λ(x⁻¹)·(x₁⋯x_N)^s = s_{w₀λ+s}(x)`

Analytic fact **(b)** behind the contragredient identity (Etingof §5.22-5.23,
issue #5526 / #5534). The `det^s`-twist of the (negative-weight) linear-dual
character collapses back into a genuine `schurPoly`. Concretely, for a weight
`λ : Fin N → ℕ` and a shift `s ≥ λ₀`, the substitution `xᵢ ↦ xᵢ⁻¹` followed by
multiplication by `(x₁⋯x_N)^s` sends `s_λ` to `s_ν`, where
`ν j = s - λ_{w₀ j} = s - λ_{rev j}` is the `w₀`-twisted, `s`-shifted weight.

Since the repo works with honest polynomials (`schurPoly N : (Fin N → ℕ) →
MvPolynomial (Fin N) ℚ`, no Laurent variables), the inverse substitution is
encoded *honestly* as the **complemented-exponent alternant**
`det(Xᵢ^{(s+N-1) - (λ_j + δ_j)})`, which equals `(x₁⋯x_N)^{s+N-1}·a_{λ+δ}(x⁻¹)`
(every exponent is nonnegative because `λ_j + δ_j ≤ λ₀ + N - 1 ≤ s + N - 1`).
Reversing the columns of this alternant turns the exponent sequence into the
shifted-exponent sequence of `ν` (up to the sign of the reversal permutation),
so its determinant is `ε · s_ν · Δ` with `ε = sgn(w₀)` and `Δ` the Vandermonde.

The proof is pure alternant linear algebra: the column reversal `Fin.revPerm`
identity (`Matrix.det_permute'`) plus the alternant-ratio defining property of
`schurPoly` (`schurPoly_mul_vandermonde`). No `formalCharacter`, no representation
theory. The consumer
(`exists_common_schurModule_model_detTwist_dual`, `ContragredientIdentity.lean`)
combines this with fact (a) (`FormalCharacterDual.lean`).
-/

noncomputable section

namespace Etingof

open MvPolynomial

/-- The `w₀`-twisted, `s`-shifted weight `ν j = s - λ_{rev j}`. For `λ` antitone
and `s ≥ λ₀` this is again an antitone `ℕ`-weight; it is `(λ.w0Twist).toNatWeight`
in the integer-weight bookkeeping of `Theorem5_23_2Core.lean`. -/
def w0ShiftWeight (N : ℕ) (lam : Fin N → ℕ) (s : ℕ) : Fin N → ℕ :=
  fun j => s - lam (Fin.rev j)

/-- For antitone `λ`, the `w₀`-twisted `s`-shifted weight `ν j = s - λ_{rev j}`
is antitone. -/
theorem w0ShiftWeight_antitone (N : ℕ) (lam : Fin N → ℕ) (hlam : Antitone lam)
    (s : ℕ) : Antitone (w0ShiftWeight N lam s) := by
  intro i j hij
  have h := hlam (Fin.rev_anti hij)
  simp only [w0ShiftWeight]
  omega

/-- The complemented-exponent sequence `(s+N-1) - (λ_j + δ_j)` equals the
shifted-exponent sequence of `ν = w0ShiftWeight λ s` read with reversed columns. -/
private theorem complementExps_eq (N : ℕ) (lam : Fin N → ℕ) (s : ℕ)
    (hs : ∀ j, lam j ≤ s) :
    (fun j => (s + N - 1) - shiftedExps N lam j)
      = fun j => shiftedExps N (w0ShiftWeight N lam s) (Fin.rev j) := by
  funext j
  have hj := hs j
  have hjlt := j.isLt
  simp only [shiftedExps, w0ShiftWeight, Fin.rev_rev, Fin.val_rev]
  omega

/-- **The inverted-variable Schur identity (fact (b)), honest form.**

For a weight `λ : Fin N → ℕ` and `s : ℕ` with `λ_j ≤ s` for all `j`, the
complemented-exponent alternant `det(Xᵢ^{(s+N-1) - (λ_j+δ_j)})` — which is the
honest avatar of `(x₁⋯x_N)^{s+N-1}·a_{λ+δ}(x⁻¹)` — equals `sgn(w₀)` times
`s_ν · Δ`, where `ν j = s - λ_{rev j}` and `Δ` is the Vandermonde determinant.

Cancelling the common Vandermonde from numerator and denominator of the
alternant ratio (the denominator `a_δ(x⁻¹)` contributes the *same* `sgn(w₀)`)
this is exactly `s_λ(x⁻¹)·(x₁⋯x_N)^s = s_ν(x)`. -/
theorem schurPoly_inverseShift (N : ℕ) (lam : Fin N → ℕ) (s : ℕ)
    (hs : ∀ j, lam j ≤ s) :
    (alternantMatrix N (fun j => (s + N - 1) - shiftedExps N lam j)).det
      = (↑↑(Fin.revPerm (n := N)).sign : MvPolynomial (Fin N) ℚ) *
          (schurPoly N (w0ShiftWeight N lam s) *
            (alternantMatrix N (vandermondeExps N)).det) := by
  rw [complementExps_eq N lam s hs]
  have hmat :
      alternantMatrix N (fun j => shiftedExps N (w0ShiftWeight N lam s) (Fin.rev j))
        = (alternantMatrix N (shiftedExps N (w0ShiftWeight N lam s))).submatrix
            id Fin.revPerm := by
    ext i j
    simp only [alternantMatrix, Matrix.of_apply, Matrix.submatrix_apply, id_eq,
      Fin.revPerm_apply]
  rw [hmat, Matrix.det_permute', schurPoly_mul_vandermonde]

end Etingof
