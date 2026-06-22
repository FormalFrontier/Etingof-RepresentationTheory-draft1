import Mathlib
import EtingofRepresentationTheory.Chapter5.CauchyWeightSpaceDimension
import EtingofRepresentationTheory.Chapter5.FormalCharacterIso
import EtingofRepresentationTheory.Chapter5.CauchySchurBasis

/-!
# Assembly of the right-`GL_N` Cauchy character identity

This file discharges the residual assembly of issue #4944: the right-`GL_N`
Cauchy character identity `polyRightDegreeFDRep_formalCharacter`. The theorem is
the `FDRep`-level statement

  `formalCharacter k N (A_d) = ∑_{ν : BoundedPartition N d} s_ν(1,…,1) · S_ν`,

with multiplicity `s_ν(1,…,1) = eval (1,…,1) (schurPoly N ν.parts)` (the
dimension of the left Schur-module factor `S_ν(k^N)`).

## Layering

The proof needs the weight-space coefficient computation of #4957,
`formalCharacter_polyRightDegreeFDRep_coeff` (`CauchyWeightSpaceDimension.lean`),
which lives *downstream* of `polyRightDegreeFDRep`'s definition file
(`CauchyCharacterRight.lean`). The deliverable theorem therefore cannot be proved
in `CauchyCharacterRight.lean` itself without a circular import, so it is
assembled here and re-opened under the original `Etingof.CauchyCharacterRight`
namespace, keeping its fully-qualified name `polyRightDegreeFDRep_formalCharacter`
unchanged.

## The two coefficient ingredients

By `MvPolynomial.ext`, the identity is checked coefficient-by-coefficient at each
weight `μ : Fin N →₀ ℕ`:

* **Sub-issue A (#4957, landed):** the left-hand-side coefficient
  `(formalCharacter k N (A_d)).coeff μ` equals `∏_j C(μ_j + N − 1, N − 1)` when
  `∑_j μ_j = d` and `0` otherwise (`formalCharacter_polyRightDegreeFDRep_coeff`).
* **Sub-issue B (#4958, symmetric-function Cauchy core):** the right-hand-side
  coefficient `∑_ν s_ν(1^N) · (schurPoly N ν.parts).coeff μ` equals the same
  count `∏_j C(μ_j + N − 1, N − 1)` (for `∑_j μ_j = d`). This is stated below as
  `cauchy_schur_coeff_multichoose`, the named dependency on #4958; its proof
  (the Schur-basis Cauchy identity at `y = 1^N`) is tracked in #4958 and lands
  there. Off the degree-`d` locus both sides vanish: each `schurPoly N ν.parts`
  is homogeneous of degree `∑_i ν.parts_i = d` (`schurPoly_isHomogeneous`), so its
  `μ`-coefficient is `0` whenever `∑_j μ_j ≠ d`.

The two ingredients meet exactly at `∏_j C(μ_j + N − 1, N − 1)`, and the assembly
is the `ext` plus the termwise `coeff_sum`/`coeff_smul` rewrite chaining A
through B.
-/

namespace Etingof.CauchyCharacterRight

open MvPolynomial Etingof Etingof.PolynomialGLAction Etingof.PolyRightGrading
  Etingof.CauchyWeightSpaceDimension

/-- **Symmetric-function Cauchy core.**
For every weight `μ : Fin N →₀ ℕ` of total degree `d`, the Schur-basis Cauchy
multiplicity sum at `y = 1^N` equals the multichoose count:

  `∑_ν s_ν(1^N) · (schurPoly N ν.parts).coeff μ = ∏_j C(μ_j + N − 1, N − 1)`.

This is the right-hand-side coefficient of the Cauchy character identity (the
Schur-basis Cauchy identity specialised at `y = (1,…,1)` and truncated to degree
`d`). The proof is `Etingof.CauchySchurBasis.cauchy_schur_coeff`; here the RHS is
the cast of a `ℕ`-product, bridged by `Nat.cast_prod`. -/
theorem cauchy_schur_coeff_multichoose (N d : ℕ) (μ : Fin N →₀ ℕ)
    (hμ : ∑ j, μ j = d) :
    ∑ ν : BoundedPartition N d,
        (MvPolynomial.eval (fun _ => (1 : ℚ)) (schurPoly N ν.parts))
          * (schurPoly N ν.parts).coeff μ
      = ((∏ j, (μ j + N - 1).choose (N - 1) : ℕ) : ℚ) := by
  simpa [Nat.cast_prod] using
    Etingof.CauchySchurBasis.cauchy_schur_coeff (N := N) (d := d) μ hμ

/-- **The right-`GL_N` Cauchy character identity** (residual assembly of #4944).
As a right-`GL_N`-representation, the total-degree-`d` part of `A = k[Xᵢⱼ]` is the
sum, over the dominant weights `ν ∈ ℕ^N` of size `d` (`BoundedPartition N d`), of
the irreducibles `V_ν` each with multiplicity `dim S_ν(k^N) = s_ν(1,…,1)`:

  `formalCharacter k N (A_d) = ∑_{ν : BoundedPartition N d} s_ν(1,…,1) · S_ν`.

The multiplicity `s_ν(1,…,1)` is `schurPoly` evaluated at the all-ones point
(the dimension of the left Schur-module factor, i.e. the number of SSYT of shape
`ν` with entries in `[N]`).

Proof: `MvPolynomial.ext` reduces to a per-weight coefficient identity. The
left-hand-side coefficient is #4957's count `∏_j C(μ_j+N−1, N−1)`
(`formalCharacter_polyRightDegreeFDRep_coeff`); the right-hand-side coefficient is
the same count by `cauchy_schur_coeff_multichoose` (#4958). Off the degree-`d`
locus both vanish (the left side by #4957's `if`, the right side by
homogeneity of `schurPoly N ν.parts`). -/
theorem polyRightDegreeFDRep_formalCharacter
    (k : Type*) [Field k] [IsAlgClosed k] [CharZero k] (N d : ℕ) :
    formalCharacter k N (polyRightDegreeFDRep k N d)
      = ∑ ν : BoundedPartition N d,
          (MvPolynomial.eval (fun _ => (1 : ℚ)) (schurPoly N ν.parts)) •
            schurPoly N ν.parts := by
  apply MvPolynomial.ext
  intro μ
  rw [formalCharacter_polyRightDegreeFDRep_coeff, MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_smul, smul_eq_mul]
  by_cases h : (∑ j, μ j) = d
  · rw [if_pos h]
    exact (cauchy_schur_coeff_multichoose N d μ h).symm
  · rw [if_neg h]
    refine (Finset.sum_eq_zero ?_).symm
    intro ν _
    have hdeg : (schurPoly N ν.parts).coeff μ = 0 :=
      (schurPoly_isHomogeneous N ν.parts).coeff_eq_zero
        (by rw [Finsupp.degree_eq_sum, ν.sum_eq]; exact h)
    rw [hdeg, mul_zero]

end Etingof.CauchyCharacterRight
