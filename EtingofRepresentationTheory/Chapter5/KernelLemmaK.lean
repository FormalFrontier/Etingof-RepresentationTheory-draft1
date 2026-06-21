import Mathlib
import EtingofRepresentationTheory.Chapter5.DetPowerFiltration

/-!
# The det⁻¹-elimination kernel lemma (K) and its functions-on-`GL` interface

This file assembles the **kernel lemma (K)** of the det⁻¹-elimination program
(issue #4694, route doc `progress/kernel-lemma-K-route.md`) from the two
prerequisites now in place:

* the det-power filtration `A_r = det⁻ʳ·A` of `O = A[det⁻¹]`, its `GL_N`-stability,
  and the equivariant subquotient iso `A_r/A_{r-1} ≅ (A/det) ⊗ χ⁻ʳ`
  (`DetPowerFiltration.lean`);
* the representation-theoretic core (K′): for `r ≥ 1` the twisted quotient
  `(A/det) ⊗ χ⁻ʳ` has no nonzero nonneg-weight submodule
  (`kernelLemmaK'_submodule`, currently a sorry'd dependency tracked by #4832).

## (K), det-power-descent form

`kernelLemmaK`: a finite family `w : ι → O` of right-torus **weight vectors** with
weights in `ℕ^N`, spanning a right-`GL_N`-stable subspace, lands in the polynomial
subring `A` (each `w i ∈ range (algebraMap A O)`).

The proof is the **det-power descent**. The family spans a subspace `W ⊆ A_R` for
`R = ⨆ⱼ detExp (w j)` (finite). For `r ≥ 1` with `W ⊆ A_r`, the subquotient image
`W̄ ⊆ A_r/A_{r-1} ≅ (A/det)⊗χ⁻ʳ` is a nonneg-weight submodule (the generators are
weight vectors with weights in `ℕ^N`, and `filtrToQuot` preserves weights since it
intertwines the actions), so `W̄ = ⊥` by (K′); hence every generator lies in
`ker filtrToQuot = A_{r-1}`, i.e. `W ⊆ A_{r-1}`. Descending to `r = 0` puts `W` in
`A_0 = A`.

The right-`GL_N`-stability hypothesis `hstable` is the mathematically load-bearing
input to (K) (it excludes e.g. `span{X₁₁X₂₂·det⁻¹}`, a single nonneg-weight vector
outside `A`); it becomes essential in the descent once (K′) is given its corrected
GL-submodule form (see #4832). It is carried here so the statement is the genuine
book lemma.

## Functions-on-`GL` interface (consumed by #4695)

`kernelLemmaK_evalGL` / `kernelLemmaK_evalAtGL`: under the same hypotheses, each
`w i` (resp. each `evalAtGL`-coefficient) is `eval`-equal on **all** of `GL_N` to a
bare-entry polynomial `Q ∈ A`. This is the form `detInv_elim_of_polynomial` (#4695)
consumes.
-/

namespace Etingof.KernelLemmaK

open MvPolynomial Etingof.PolynomialGLAction Etingof.DetLocalization
  Etingof.LocalizationGLAction Etingof.KernelLemmaKPrime Etingof.DetPowerFiltration

variable {k : Type*} [Field k] {N : ℕ}

/-! ### Weight-space bookkeeping -/

/-- Membership in the integer weight space, unfolded: `v` is a weight-`ν` vector
iff every diagonal torus element `diagUnit i t` scales it by `t ^ ν i`. -/
theorem mem_glWeightSpaceℤ_iff {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k (Matrix.GeneralLinearGroup (Fin N) k) V)
    (ν : Fin N → ℤ) (v : V) :
    v ∈ glWeightSpaceℤ k N ρ ν
      ↔ ∀ (i : Fin N) (t : kˣ), ρ (diagUnit k N i t) v = ((t ^ ν i : kˣ) : k) • v := by
  simp only [glWeightSpaceℤ, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_coe, id_eq, sub_eq_zero]

/-- **`filtrToQuot` preserves weights.** A weight-`ν` vector of the right-translation
representation on `A_r` maps to a weight-`ν` vector of the twisted quotient
`(A/det) ⊗ χ⁻ʳ`: intertwiners preserve torus weights, and `filtrToQuot` intertwines
`localRightRep` with `quotDetTwistRep` (`filtrToQuot_equivariant`). -/
theorem filtrToQuot_mem_glWeightSpaceℤ (r : ℕ) (x : ↥(filtrA k N r)) (ν : Fin N → ℤ)
    (hx : (x : Localization.Away (detPoly k N))
            ∈ glWeightSpaceℤ k N (localRightRep k N) ν) :
    filtrToQuot k N r x ∈ glWeightSpaceℤ k N (quotDetTwistRep k N r) ν := by
  rw [mem_glWeightSpaceℤ_iff] at hx ⊢
  intro i t
  rw [← filtrToQuot_equivariant (diagUnit k N i t) r x]
  have hsub : (⟨localRightRep k N (diagUnit k N i t) (x : Localization.Away (detPoly k N)),
        localRightRep_mem_filtrA (diagUnit k N i t) r x.2⟩ : ↥(filtrA k N r))
      = ((t ^ ν i : kˣ) : k) • x := by
    apply Subtype.ext
    rw [SetLike.val_smul]
    exact hx i t
  rw [hsub, map_smul]

/-! ### The kernel lemma (K) -/

/-- **Kernel lemma (K).** A finite family `w : ι → O = A[det⁻¹]` of right-torus
weight vectors with weights in `ℕ^N` (`hw`), spanning a right-`GL_N`-stable subspace
(`hstable`), consists of honest polynomials: each `w i ∈ range (algebraMap A O)`.

Proved by det-power descent against (K′) (`kernelLemmaK'`); see the module
docstring. (K′) is currently a sorry'd dependency (#4832), as permitted for this
assembly. -/
theorem kernelLemmaK [IsAlgClosed k] [CharZero k] {ι : Type*} [Finite ι]
    (w : ι → Localization.Away (detPoly k N)) (μ : ι → (Fin N → ℕ))
    (hw : ∀ i, w i ∈ glWeightSpaceℤ k N (localRightRep k N) (fun j => (μ i j : ℤ)))
    (hstable : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k),
        ∀ x ∈ Submodule.span k (Set.range w),
          localRightRep k N g x ∈ Submodule.span k (Set.range w))
    (i : ι) :
    w i ∈ Set.range (algebraMap (MvPolynomial (Fin N × Fin N) k)
      (Localization.Away (detPoly k N))) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  set W := Submodule.span k (Set.range w) with hW
  -- Descent step: `W ⊆ A_{r+1} ⟹ W ⊆ A_r`.
  have step : ∀ r : ℕ, W ≤ filtrA k N (r + 1) → W ≤ filtrA k N r := by
    intro r hWsucc
    have hgen : ∀ j, w j ∈ filtrA k N r := by
      intro j
      have hwj : w j ∈ filtrA k N (r + 1) := hWsucc (Submodule.subset_span ⟨j, rfl⟩)
      -- The subquotient image of `w j` is a nonneg-weight vector, hence `0` by (K′).
      have hquot : filtrToQuot k N (r + 1) ⟨w j, hwj⟩ = 0 := by
        have hmem : filtrToQuot k N (r + 1) ⟨w j, hwj⟩
            ∈ ⨆ (ν : Fin N → ℕ),
                glWeightSpaceℤ k N (quotDetTwistRep k N (r + 1)) (fun l => (ν l : ℤ)) :=
          Submodule.mem_iSup_of_mem (μ j)
            (filtrToQuot_mem_glWeightSpaceℤ (r + 1) ⟨w j, hwj⟩ _ (hw j))
        rw [kernelLemmaK' k N (r + 1) (by omega)] at hmem
        simpa using hmem
      -- `filtrToQuot (w j) = 0 ⟹ w j ∈ A_r` (`ker filtrToQuot = A_r` inside `A_{r+1}`).
      have hker : (⟨w j, hwj⟩ : ↥(filtrA k N (r + 1)))
          ∈ LinearMap.ker (filtrToQuot k N (r + 1)) := LinearMap.mem_ker.2 hquot
      rw [ker_filtrToQuot (r + 1) (by omega)] at hker
      simpa using hker
    exact Submodule.span_le.mpr (Set.range_subset_iff.mpr hgen)
  -- Descend from any `A_r` down to `A_0`.
  have descend : ∀ r : ℕ, W ≤ filtrA k N r → W ≤ filtrA k N 0 := by
    intro r
    induction r with
    | zero => exact id
    | succ r ih => intro h; exact ih (step r h)
  -- `W ⊆ A_R` for `R = ⨆ⱼ detExp (w j)` (finite family).
  have hWR : W ≤ filtrA k N (Finset.univ.sup (fun j => detExp (w j))) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, mem_filtrA_iff_detExp]
    exact Finset.le_sup (f := fun j => detExp (w j)) (Finset.mem_univ j)
  have hW0 : W ≤ filtrA k N 0 := descend _ hWR
  have hwi0 : w i ∈ filtrA k N 0 := hW0 (Submodule.subset_span ⟨i, rfl⟩)
  rw [mem_filtrA_iff_detExp] at hwi0
  exact (detExp_eq_zero_iff (w i)).mp (Nat.le_zero.mp hwi0)

/-! ### Functions-on-`GL` interface -/

/-- **Functions-on-`GL` form of (K)** (consumed by #4695). Under the kernel-lemma
hypotheses, each localization element `w i` is `eval`-equal on **all** of `GL_N` to
a bare-entry polynomial `Q ∈ A = k[Xᵢⱼ]`: `evalGLAway (w i) g = eval g Q`. -/
theorem kernelLemmaK_evalGL [IsAlgClosed k] [CharZero k] {ι : Type*} [Finite ι]
    (w : ι → Localization.Away (detPoly k N)) (μ : ι → (Fin N → ℕ))
    (hw : ∀ i, w i ∈ glWeightSpaceℤ k N (localRightRep k N) (fun j => (μ i j : ℤ)))
    (hstable : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k),
        ∀ x ∈ Submodule.span k (Set.range w),
          localRightRep k N g x ∈ Submodule.span k (Set.range w))
    (i : ι) :
    ∃ Q : MvPolynomial (Fin N × Fin N) k, ∀ g : Matrix.GeneralLinearGroup (Fin N) k,
      evalGLAway (w i) g
        = MvPolynomial.eval
            (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2) Q := by
  obtain ⟨Q, hQ⟩ := kernelLemmaK w μ hw hstable i
  refine ⟨Q, fun g => ?_⟩
  rw [← hQ, evalGLAway_algebraMap, evalGLHom_apply]

/-- **`evalAtGL` form of (K)** (consumed by #4695). If the `evalAtGL`-coefficients
`evalAtGL g (P i)` arise from `P i ∈ k[Xᵢⱼ, D]` whose localization images
`coordToAway (P i)` are nonneg-weight vectors spanning a `GL_N`-stable subspace,
then each is `eval`-equal on all of `GL_N` to a bare-entry polynomial `Q ∈ k[Xᵢⱼ]`
(the `D = det⁻¹` variable is eliminated). -/
theorem kernelLemmaK_evalAtGL [IsAlgClosed k] [CharZero k] {ι : Type*} [Finite ι]
    (P : ι → MvPolynomial (Etingof.GLCoordVars N) k) (μ : ι → (Fin N → ℕ))
    (hw : ∀ i, coordToAway (P i)
            ∈ glWeightSpaceℤ k N (localRightRep k N) (fun j => (μ i j : ℤ)))
    (hstable : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k),
        ∀ x ∈ Submodule.span k (Set.range fun i => coordToAway (P i)),
          localRightRep k N g x ∈ Submodule.span k (Set.range fun i => coordToAway (P i)))
    (i : ι) :
    ∃ Q : MvPolynomial (Fin N × Fin N) k, ∀ g : Matrix.GeneralLinearGroup (Fin N) k,
      Etingof.evalAtGL g (P i)
        = MvPolynomial.eval
            (fun ij : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) k) ij.1 ij.2) Q := by
  obtain ⟨Q, hQ⟩ := kernelLemmaK_evalGL (fun i => coordToAway (P i)) μ hw hstable i
  refine ⟨Q, fun g => ?_⟩
  rw [evalAtGL_eq_evalGLAway_coordToAway, hQ]

end Etingof.KernelLemmaK
