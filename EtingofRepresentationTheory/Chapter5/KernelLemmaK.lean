import Mathlib
import EtingofRepresentationTheory.Chapter5.KernelLemmaKPrime
import EtingofRepresentationTheory.Chapter5.DetPowerFiltration

/-!
# The kernel lemma (K): assembling the det⁻¹-elimination from (K′)

This file builds the **det-power-filtration assembly** that derives the full
kernel lemma (K) — *a nonnegative-weight, right-`GL_N`-stable submodule of
`O = A[det⁻¹]` lies in the polynomial subring `A`* — from the deep core (K′)
(`Etingof.KernelLemmaKPrime.kernelLemmaK'_submodule`) via the increasing
filtration `A_r = det⁻ʳ · A` (`Etingof.DetPowerFiltration`).

The geometry: `O = ⋃_r A_r` (`iSup_filtrA`), the steps are `GL_N`-stable
(`localRightRep_mem_filtrA`), and the subquotient is the twisted quotient
`A_r / A_{r-1} ≅ (A/det) ⊗ χ⁻ʳ` (`filtrToQuot`, `filtrToQuot_equivariant`).
A nonneg-weight submodule meeting `A_r` (`r ≥ 1`) maps to a nonneg-weight
submodule of `(A/det) ⊗ χ⁻ʳ`, which (K′) forces to be `⊥`; so it already lay in
`A_{r-1}`. Descending the filtration lands it in `A_0 = A`.

## Contents

* `glWeightSpaceℤ_map_le` / `glWeightSpaceℤ_iSup_map_le` — **functoriality** of the
  integer weight spaces: a `GL_N`-equivariant `k`-linear map sends the `μ`-weight
  space into the `μ`-weight space (and the supremum of nonneg-weight spaces into
  the supremum of nonneg-weight spaces). Reusable keystone for transporting the
  nonnegativity hypothesis across the subquotient map.
* `kernelLemmaK_step` — **one filtration step** (sorry-free): if the image of a
  submodule `W ⊆ A_r` (`r ≥ 1`) under `filtrToQuot` is nonneg-weight, then
  `W ⊆ A_{r-1}`. This is the direct contradiction against (K′).

The remaining ingredient for the full descent — that the *image* nonnegativity
hypothesis of `kernelLemmaK_step` follows from nonnegativity of `W` itself —
requires torus-semisimplicity of `O` over `ℤ`-weights (every torus-stable
submodule is the sum of its weight pieces), which is **not** yet available in the
repo for the infinite-dimensional `O`. That gap, and the final `det⁻¹`-elimination
wiring (`detInv_elim_of_polynomial`, #4695), are tracked separately.
-/

open MvPolynomial

namespace Etingof.KernelLemmaKPrime

variable {k : Type*} [Field k] {N : ℕ}

/-! ### Functoriality of integer weight spaces -/

/-- **Functoriality of `glWeightSpaceℤ`.** A `GL_N`-equivariant `k`-linear map
`φ : V → W` (intertwining `ρV` and `ρW`) sends the `μ`-weight space into the
`μ`-weight space: `(M_μ).map φ ≤ N_μ`. Only the intertwining property is needed,
so `φ` may be any linear map (not necessarily an equivalence). -/
theorem glWeightSpaceℤ_map_le {V W : Type*}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρV : Representation k (Matrix.GeneralLinearGroup (Fin N) k) V)
    (ρW : Representation k (Matrix.GeneralLinearGroup (Fin N) k) W)
    (φ : V →ₗ[k] W)
    (hφ : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (v : V), φ (ρV g v) = ρW g (φ v))
    (μ : Fin N → ℤ) :
    (glWeightSpaceℤ k N ρV μ).map φ ≤ glWeightSpaceℤ k N ρW μ := by
  rw [Submodule.map_le_iff_le_comap]
  intro v hv
  simp only [glWeightSpaceℤ, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_coe, id_eq, Submodule.mem_comap] at hv ⊢
  intro i t
  have h : ρV (diagUnit k N i t) v = (((t ^ μ i : kˣ) : k)) • v := sub_eq_zero.mp (hv i t)
  have hW : ρW (diagUnit k N i t) (φ v) = (((t ^ μ i : kˣ) : k)) • φ v := by
    rw [← hφ, h, map_smul]
  exact sub_eq_zero.mpr hW

/-- **Functoriality on the supremum of weight spaces.** An equivariant `φ` sends a
supremum of weight spaces into the corresponding supremum; in particular it sends
the supremum of nonneg-weight spaces into the supremum of nonneg-weight spaces. -/
theorem glWeightSpaceℤ_iSup_map_le {V W : Type*}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρV : Representation k (Matrix.GeneralLinearGroup (Fin N) k) V)
    (ρW : Representation k (Matrix.GeneralLinearGroup (Fin N) k) W)
    (φ : V →ₗ[k] W)
    (hφ : ∀ (g : Matrix.GeneralLinearGroup (Fin N) k) (v : V), φ (ρV g v) = ρW g (φ v))
    {ι : Type*} (μs : ι → (Fin N → ℤ)) :
    (⨆ i, glWeightSpaceℤ k N ρV (μs i)).map φ ≤ ⨆ i, glWeightSpaceℤ k N ρW (μs i) := by
  rw [Submodule.map_iSup]
  exact iSup_mono fun i => glWeightSpaceℤ_map_le ρV ρW φ hφ (μs i)

/-! ### One filtration step against (K′) -/

open Etingof.DetPowerFiltration Etingof.DetLocalization

variable [IsAlgClosed k] [CharZero k]

/-- **One descent step of the det-power filtration.** Let `W ⊆ A_r` be a submodule
of `O` (`r ≥ 1`) whose image under the subquotient map `filtrToQuot k N r` is a
*nonnegative-weight* submodule of `(A/det) ⊗ χ⁻ʳ`. Then (K′)
(`kernelLemmaK'_submodule`) forces that image to be `⊥`, i.e. `filtrToQuot` kills
`W`; equivalently `W ⊆ A_{r-1}`.

This is the sorry-free contradiction half of the filtration descent. Supplying
the image-nonnegativity hypothesis from nonnegativity of `W` itself is the
remaining ingredient (torus-semisimplicity of `O`), tracked separately. -/
theorem kernelLemmaK_step (r : ℕ) (hr : 1 ≤ r)
    {W : Submodule k (Localization.Away (detPoly k N))}
    (hWr : W ≤ filtrA k N r)
    (hWnn : Submodule.map (filtrToQuot k N r) (W.comap (filtrA k N r).subtype) ≤
      ⨆ (μ : Fin N → ℕ), glWeightSpaceℤ k N (quotDetTwistRep k N r) (fun i => (μ i : ℤ))) :
    W ≤ filtrA k N (r - 1) := by
  -- (K′) collapses the image to `⊥`.
  have hbot : Submodule.map (filtrToQuot k N r) (W.comap (filtrA k N r).subtype) = ⊥ :=
    kernelLemmaK'_submodule k N r hr hWnn
  -- Read off `W ⊆ A_{r-1}` element-wise: `filtrToQuot` kills `W ∩ A_r`, and its
  -- kernel is `A_{r-1} ∩ A_r` (`ker_filtrToQuot`).
  intro w hw
  have hwr : w ∈ filtrA k N r := hWr hw
  have hx : (⟨w, hwr⟩ : ↥(filtrA k N r)) ∈ W.comap (filtrA k N r).subtype := hw
  have hker : filtrToQuot k N r ⟨w, hwr⟩ = 0 := by
    have hmem : filtrToQuot k N r ⟨w, hwr⟩ ∈
        Submodule.map (filtrToQuot k N r) (W.comap (filtrA k N r).subtype) :=
      Submodule.mem_map_of_mem hx
    rw [hbot, Submodule.mem_bot] at hmem
    exact hmem
  have hmem' : (⟨w, hwr⟩ : ↥(filtrA k N r)) ∈
      (filtrA k N (r - 1)).comap (filtrA k N r).subtype := by
    rw [← ker_filtrToQuot r hr, LinearMap.mem_ker]; exact hker
  rwa [Submodule.mem_comap, Submodule.coe_subtype] at hmem'

end Etingof.KernelLemmaKPrime
