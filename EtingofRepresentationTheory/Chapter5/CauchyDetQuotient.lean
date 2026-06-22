import Mathlib
import EtingofRepresentationTheory.Chapter5.KernelLemmaKPrime
import EtingofRepresentationTheory.Chapter5.Theorem5_23_2
import EtingofRepresentationTheory.Chapter5.DetShiftIso

/-!
# Cauchy decomposition of the determinant quotient: constituents have `ν_N = 0`

This file states the **part (a)** deliverable of the kernel-lemma-K′ core
(issue #4896, parent #4890, route doc `progress/kernel-lemma-K-route.md`): the
`GL_N × GL_N`-equivariant **Cauchy** content pinning the last highest-weight
coordinate of every irreducible constituent of the determinant quotient

  `A/det = k[Xᵢⱼ]/(det)`     (`quotDetRep`, `KernelLemmaKPrime.lean`)

to `ν_N = 0`. The sibling **part (b)** (issue #4897) consumes this to realize a
negative lowest weight after the `χ⁻ʳ` twist and discharge
`quotDetTwist_nonzero_subrep_has_neg_weight` (`KernelLemmaKPrime.lean:261`).

## The statement and how part (b) consumes it

`quotDetRep_irreducible_constituent_lastWeight_zero` says: an irreducible
finite-dimensional `GL_N`-representation `L` that embeds `GL_N`-equivariantly
into `A/det = k[Xᵢⱼ]/(det)` has formal character `schurPoly N ν` for a partition
`ν` (antitone, `ν ∈ ℕ^N`) whose **last coordinate is `0`**. Equivalently, in the
highest-weight classification of polynomial `GL_N`-irreps via formal characters
(`iso_of_formalCharacter_eq_schurPoly`, `SchurWeylFormalCharacterIso.lean`), the
highest weight `ν` of `L` satisfies `ν_N = 0`.

The interface is phrased exactly as the project's other highest-weight
classification statements (`schurWeyl_simples_formalCharacter_classification_core`,
`SchurWeylSimplesClassification.lean`):

* irreducibility of `L` is
  `IsSimpleModule (MonoidAlgebra k (GL (Fin N) k)) (Representation.asModule L.ρ)`;
* the highest weight is read off as `formalCharacter k N L = schurPoly N ν`,
  with the extra arithmetic datum `(0 : ℕ) ∈ Set.range ν`. For an antitone
  `ν : Fin N → ℕ` (`N ≥ 1`) the minimum entry is the last one and all entries are
  `≥ 0`, so `0 ∈ Set.range ν` is exactly the route-doc condition `ν_N = 0`. (We
  avoid `ν (Fin.last N)` since `Fin.last N : Fin (N + 1)` does not index a
  `Fin N`-weight for a variable `N`.)

The embedding of `L` as a constituent of the *infinite-dimensional* quotient
`A/det` is a `GL_N`-equivariant injection `φ : L →ₗ[k] (A/det)` (we cannot use
`FDRep.of (quotDetRep …)` because `A/det` is not finite-dimensional). Part (b)
extracts such an `L` and `φ` from a finite-dimensional subrepresentation by
complete reducibility (`Theorem5_23_2_i`).

## Why this is the genuine gap (no torus shortcut)

`Theorem5_23_2_ii` is **rank-only** (`nonempty_linearEquiv_of_rank_eq`): it
carries no weight or `GL × GL`-equivariance data and cannot read off the weight
structure of constituents. The forbidden shortcuts — column-sum `≥ r`, rank-only
Peter–Weyl, one- or two-sided torus nonnegativity — are each defeated by the
`N = 2, r = 1` example `α X₁₁X₂₂ + β X₁₂X₂₁` (route doc §"Why the torus alone is
insufficient"). The real content is the **`GL_N × GL_N`-equivariant Cauchy
decomposition**

  `k[Xᵢⱼ] = ⊕_{ν ∈ ℕ^N dom} V_ν^* ⊠ V_ν`    (each `ν` with multiplicity one)

together with the highest-weight shift `det · A ≅ A ⊗ χ`
(`detShiftLinearEquiv_intertwine`, `DetShiftIso.lean:152`, already sorry-free):
multiplication by `det` raises every constituent's highest weight by `(1,…,1)`,
so the constituents of `A/det = A / (det · A)` are exactly the `ν` *not* of the
form `μ + (1,…,1)`, i.e. those with `ν_N = 0`.

## Status (decomposition of #4896)

The proof requires three pieces of infrastructure that the repository (and
Mathlib) currently lack; #4896 is decomposed into self-contained successors that
build them, and this file fixes the **consumable statement** (top-down):

1. a genuine `GL_N`-representation structure on `AlgIrrepGL` (currently a bare
   `k`-module — `Theorem5_23_2.lean:86`);
2. the right-`GL_N` homogeneous grading of `k[Xᵢⱼ]` (each total-degree component
   is a subrepresentation; `det` is homogeneous of degree `N`), giving the
   per-degree short exact sequence `0 → A_{d-N} ⊗ χ → A_d → (A/det)_d → 0`;
3. the `GL_N × GL_N`-equivariant Cauchy multiplicity-one decomposition of
   `k[Xᵢⱼ]` (the research-level epic).

The single `sorry` below is the assembly of (1)+(2)+(3) with the sorry-free
det-shift; it is tracked by the successor issues filed against #4896.
-/

namespace Etingof.KernelLemmaKPrime

open MvPolynomial Etingof Etingof.PolynomialGLAction

/-- **(K′) part (a): constituents of `A/det` have last highest-weight coordinate
`ν_N = 0`.** Let `L` be an irreducible finite-dimensional `GL_N`-representation
that embeds `GL_N`-equivariantly into the determinant quotient
`A/det = k[Xᵢⱼ]/(det)` (`quotDetRep`). Then `L` is a *polynomial* irrep: its
formal character is `schurPoly N ν` for an antitone `ν : Fin N → ℕ`, and moreover
the last (= smallest, by antitonicity) coordinate vanishes, recorded as
`(0 : ℕ) ∈ Set.range ν`.

This is the `GL_N × GL_N`-equivariant **Cauchy decomposition** of `k[Xᵢⱼ]`
together with the `det · A ≅ A ⊗ χ` highest-weight shift
(`detShiftLinearEquiv_intertwine`, sorry-free): every constituent of `A` has a
dominant highest weight `ν ∈ ℕ^N` appearing with multiplicity one, and
multiplication by `det` shifts `ν ↦ ν + (1,…,1)`, so `A/det = A / (det·A)` keeps
exactly the constituents with `ν_N = 0`.

The sibling assembly (issue #4897) consumes this — together with lowest-weight
realization (the lowest weight of an irrep of highest weight `ν` is `w₀ν`, with
last coordinate `ν_1`, and the relevant negative coordinate comes from the `χ⁻ʳ`
twist subtracting `r ≥ 1` from `ν_N = 0`) — to discharge
`quotDetTwist_nonzero_subrep_has_neg_weight`.

The proof is the residual research-level core of #4896; see the file docstring
for the decomposition into the three missing infrastructure pieces. -/
theorem quotDetRep_irreducible_constituent_lastWeight_zero
    (k : Type*) [Field k] [IsAlgClosed k] [CharZero k] (N : ℕ)
    (L : FDRep k (Matrix.GeneralLinearGroup (Fin N) k))
    (hLsimp : IsSimpleModule
      (MonoidAlgebra k (Matrix.GeneralLinearGroup (Fin N) k))
      (Representation.asModule L.ρ))
    (φ : L →ₗ[k] (MvPolynomial (Fin N × Fin N) k ⧸ detSubmodule k N))
    (hφ_inj : Function.Injective φ)
    (hφ_equiv : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (v : L),
      φ (L.ρ g v) = quotDetRep k N g (φ v)) :
    ∃ ν : Fin N → ℕ, Antitone ν ∧ (0 : ℕ) ∈ Set.range ν ∧
      formalCharacter k N L = schurPoly N ν := by
  sorry

end Etingof.KernelLemmaKPrime
