import Mathlib
import EtingofRepresentationTheory.Chapter5.Theorem5_22_1
import EtingofRepresentationTheory.Chapter5.PolyRightGrading

/-!
# The right-`GL_N` Cauchy multiplicity-one character identity on `k[Xᵢⱼ]`

This file isolates the **right-`GL_N` multiplicity form** of the Cauchy
decomposition of `A = k[Xᵢⱼ] = MvPolynomial (Fin N × Fin N) k`, the research
core (item 3) of issue #4904/#4934 and the missing infrastructure piece (3) of
the kernel-lemma-K′ deliverable (issue #4896, route doc
`progress/kernel-lemma-K-route.md`).

## What is built here (sorry-free)

The right-translation representation `polyRightRep` (`PolynomialGLRightAction.lean`)
preserves the total-degree grading (`PolyRightGrading.lean`), so each degree-`d`
homogeneous component `A_d = homogeneousSubmodule (Fin N × Fin N) k d` is a
subrepresentation (`polyRightHomogeneousSubrep`). Here we record that `A_d` is
**finite-dimensional** (`finiteDimensional_homogeneousSubmodule`: it sits inside
`restrictTotalDegree`, which is finite for finitely many variables) and package
it as a genuine `FDRep` (`polyRightDegreeFDRep`). This is the finite-dimensional
object on which `formalCharacter` (`Theorem5_22_1.lean`) is defined, so the
Cauchy decomposition can be stated as a formal-character identity.

## The Cauchy character statement (the research core)

As a right-`GL_N`-representation, the degree-`d` part of `A` is the
`GL_N × GL_N`-equivariant Cauchy decomposition of `Sym^d(V ⊗ W)` (with
`V = W = k^N` the left/right copies) read off on the right factor:

  `A_d ≅ ⊕_{ν ∈ ℕ^N dom, |ν| = d} S_ν(V) ⊗ S_ν(W)`   (each `ν` exactly once
  as a *bi*-representation),

so, forgetting the left `GL_N`-action, each right-irreducible `V_ν = S_ν(W)`
occurs with multiplicity `dim S_ν(V) = s_ν(1, …, 1)` (the number of SSYT of
shape `ν` with entries in `[N]`). On formal characters this is the Cauchy
identity specialised at `x = (1, …, 1)`:

  `formalCharacter k N (A_d) = ∑_{ν ∈ ℕ^N dom, |ν| = d} s_ν(1,…,1) · S_ν`,

equivalently `∏_j (1 - t_j)^{-N}` restricted to total degree `d`.

**The multiplicity is `s_ν(1,…,1)`, NOT one.** A *multiplicity-one* form
`formalCharacter k N (A_d) = ∑_ν S_ν` is false already on dimensions: for
`N = 2, d = 1`, `dim A_1 = 4` (the four `X_{ij}`) but `∑_{ν} dim V_ν =
dim V_{(1,0)} = 2`. The two sides disagree, because `A_d` carries the full
`dim V_ν`-fold right-multiplicity of the bi-rep, not the multiplicity-free
right factor. (See #4944 for the history; this corrected a previously false
`= ∑_ν S_ν` statement.)

The dominant weights `ν ∈ ℕ^N` with `|ν| = d` are exactly the `BoundedPartition N d`
(`Proposition5_21_1.lean`: an antitone `ν : Fin N → ℕ` with `∑ i, ν i = d`), a
finite indexing set. The identity is `polyRightDegreeFDRep_formalCharacter`,
stated here with its proof deferred to the genuine Cauchy/Schur-Weyl core
(the Cauchy identity + the highest-weight ⟺ `ν ∈ ℕ^N` theory; overlaps
`iso_of_formalCharacter_eq_schurPoly`, #4699/#4882). An elementary intermediate
form available without Schur-Weyl: the `μ`-weight space of `A_d` has dimension
`∏_j C(μ_j + N - 1, N - 1)` (monomials with column-degree vector `μ`), so
`formalCharacter k N (A_d) = ∑_{|μ| = d} (∏_j C(μ_j + N-1, N-1)) · x^μ`; the
content is rewriting this in the Schur basis.

## How the kernel lemma consumes this

Multiplying by `det` shifts every constituent's highest weight by `(1, …, 1)`
(`detShiftLinearEquiv_intertwine`, `DetShiftIso.lean`, sorry-free), and the
per-degree short exact sequence
`0 → A_{d-N} ⊗ χ → A_d → (A/det)_d → 0` (`detSubmodule_inf_homogeneous`,
`PolyRightGrading.lean`, sorry-free) is right-`GL_N`-equivariant. Hence the
multiplicity of `ν` in `(A/det)_d` is

  `mult_{A_d}(ν) − mult_{A_{d-N}}(ν − (1,…,1))`
    `= s_ν(1,…,1)·[ν ∈ ℕ^N] − s_{ν-1}(1,…,1)·[ν − 1 ∈ ℕ^N]`
    `= s_ν(1,…,1)·([ν ∈ ℕ^N] − [ν − 1 ∈ ℕ^N]) = s_ν(1,…,1)·[ν_N = 0]`,

using `dim V_{ν - (1,…,1)} = dim V_ν` (tensoring by the 1-dimensional `det`
character preserves dimension). So every irreducible constituent of `A/det`
has `ν_N = 0` — the qualitative conclusion is unchanged by the corrected
multiplicities, since they cancel termwise for `ν_N > 0`. This is exactly the
`CauchyDetQuotient.lean` deliverable
`quotDetRep_irreducible_constituent_lastWeight_zero` (#4896 part (a)); the
assembly of *this* character identity with the (already sorry-free) SES and
det-shift is tracked as a successor of #4934.
-/

namespace Etingof.CauchyCharacterRight

open MvPolynomial Etingof Etingof.PolynomialGLAction Etingof.PolyRightGrading

variable {k : Type*} [Field k] {N : ℕ}

/-- **The degree-`d` homogeneous component of `k[Xᵢⱼ]` is finite-dimensional.**
It is contained in `restrictTotalDegree (Fin N × Fin N) k d` (a homogeneous
polynomial of degree `d` has total degree `≤ d`), which is finite-dimensional
because there are finitely many variables. -/
instance finiteDimensional_homogeneousSubmodule (d : ℕ) :
    FiniteDimensional k (MvPolynomial.homogeneousSubmodule (Fin N × Fin N) k d) :=
  Submodule.finiteDimensional_of_le
      (S₂ := MvPolynomial.restrictTotalDegree (Fin N × Fin N) k d) <| by
    intro f hf
    rw [MvPolynomial.mem_restrictTotalDegree]
    exact ((MvPolynomial.mem_homogeneousSubmodule d f).1 hf).totalDegree_le

/-- **The degree-`d` homogeneous component `A_d` of `k[Xᵢⱼ]` as an `FDRep`** of
`GL_N(k)` under right translation. The carrier is the right-`GL_N`-subrepresentation
`polyRightHomogeneousSubrep k N d` (`PolyRightGrading.lean`), which is
finite-dimensional by `finiteDimensional_homogeneousSubmodule`. This is the
finite-dimensional object on which the Cauchy character identity
`polyRightDegreeFDRep_formalCharacter` is stated. -/
noncomputable def polyRightDegreeFDRep (k : Type*) [Field k] (N d : ℕ) :
    FDRep k (Matrix.GeneralLinearGroup (Fin N) k) :=
  haveI : FiniteDimensional k (polyRightHomogeneousSubrep k N d).toSubmodule :=
    finiteDimensional_homogeneousSubmodule d
  FDRep.of (polyRightHomogeneousSubrep k N d).toRepresentation

/-- **The right-`GL_N` Cauchy character identity.** As a right-`GL_N`-representation,
the total-degree-`d` part of `A = k[Xᵢⱼ]` is the sum, over the dominant weights
`ν ∈ ℕ^N` of size `d` (`BoundedPartition N d`), of the irreducibles `V_ν` each
with multiplicity `dim S_ν(k^N) = s_ν(1,…,1)`:

  `formalCharacter k N (A_d) = ∑_{ν : BoundedPartition N d} s_ν(1,…,1) · S_ν`,

where the multiplicity `s_ν(1,…,1)` is `schurPoly` evaluated at the all-ones
point (the dimension of the left Schur-module factor, i.e. the number of SSYT
of shape `ν` with entries in `[N]`).

This is the genuine research core of the `GL_N × GL_N`-equivariant Cauchy
decomposition `k[Xᵢⱼ] = ⊕_{ν ∈ ℕ^N dom} V_ν^* ⊠ V_ν` (each `ν` once *as a
bi-representation*), restricted to the right factor and read off on formal
characters. Forgetting the left action, each right-irreducible `V_ν` occurs
`dim V_ν^* = dim V_ν` times — **not** once. (A `= ∑_ν S_ν` form is false: for
`N = 2, d = 1`, `dim A_1 = 4 ≠ 2 = ∑_ν dim V_ν`. See the file header and #4944.)

Its proof is the Cauchy/Schur-Weyl content (the Cauchy identity, or the
GL×GL-equivariant decomposition of `Sym^d(V ⊗ W)`) together with the
highest-weight ⟺ `ν ∈ ℕ^N` theory; it is tracked as the residual core of #4934
(overlapping `iso_of_formalCharacter_eq_schurPoly`, #4699/#4882) and is the sole
remaining `sorry`. -/
theorem polyRightDegreeFDRep_formalCharacter
    (k : Type*) [Field k] [IsAlgClosed k] [CharZero k] (N d : ℕ) :
    formalCharacter k N (polyRightDegreeFDRep k N d)
      = ∑ ν : BoundedPartition N d,
          (MvPolynomial.eval (fun _ => (1 : ℚ)) (schurPoly N ν.parts)) •
            schurPoly N ν.parts := by
  sorry

end Etingof.CauchyCharacterRight
