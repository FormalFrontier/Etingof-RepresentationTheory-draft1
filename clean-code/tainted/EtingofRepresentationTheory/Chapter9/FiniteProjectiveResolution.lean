import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Noetherian.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Existence of a finitely generated projective resolution

For a finitely generated module `M` over a left-Noetherian ring `R`, this file constructs a
`CategoryTheory.ProjectiveResolution M` all of whose terms are *finite free* `R`-modules (in
particular finitely generated and projective). This is the existence input required to close the
finite-dimensional half of Etingof, Problem 9.4.2(iii): combined with the finiteness-propagation
results, a finitely generated module over a finite-dimensional algebra admits a projective
resolution by finite-dimensional modules.

## Construction

The resolution is built exactly like Mathlib's `CategoryTheory.ProjectiveResolution.of`, but with
the arbitrary projective covers `Projective.over`/`Projective.π` replaced by finite free covers:

* `freeCover M`, `freeCoverπ M` — a finite free module `Rⁿ` surjecting onto a finite module `M`,
  obtained from `Module.Finite.exists_fin'`.
* `syzygyMod M n` — the `n`-th syzygy, defined by `syzygyMod M 0 = M` and
  `syzygyMod M (n+1) = ker (freeCoverπ (syzygyMod M n))`. Over a Noetherian ring this stays finite
  (the kernel of a map out of a finite free module is finite).
* `Xobj M n = freeCover (syzygyMod M n)` are the terms of the resolution; each is finite free.

The exactness of the resulting complex is the finite-cover analogue of
`CategoryTheory.exact_d_f`, proved by comparing the presentation `Xₙ₊₁ → Xₙ → syzygyMod M n`
with the kernel sequence via `ShortComplex.exact_iff_of_epi_of_isIso_of_mono`.

## Main result

* `Etingof.FiniteProjectiveResolution.exists_finite_projectiveResolution` — for a finitely
  generated module `M` over a left-Noetherian ring, there is a projective resolution of `M` whose
  every term is `Module.Finite R`.
-/

universe u

open CategoryTheory Limits

namespace Etingof.FiniteProjectiveResolution

variable {R : Type u} [Ring R]

/-! ### Finite free covers -/

section FreeCover

/-- The rank of the chosen finite free cover of a finite module `M`. -/
noncomputable def coverRank (M : ModuleCat.{u} R) [Module.Finite R M] : ℕ :=
  (Module.Finite.exists_fin' R M).choose

/-- A finite free module `Rⁿ` surjecting onto the finite module `M`. -/
noncomputable def freeCover (M : ModuleCat.{u} R) [Module.Finite R M] : ModuleCat.{u} R :=
  ModuleCat.of R (Fin (coverRank M) → R)

/-- The chosen surjection `Rⁿ ↠ M` from the finite free cover. -/
noncomputable def freeCoverπ (M : ModuleCat.{u} R) [Module.Finite R M] : freeCover M ⟶ M :=
  ModuleCat.ofHom (Module.Finite.exists_fin' R M).choose_spec.choose

instance (M : ModuleCat.{u} R) [Module.Finite R M] : Module.Finite R (freeCover M) := by
  unfold freeCover ModuleCat.of; infer_instance

instance (M : ModuleCat.{u} R) [Module.Finite R M] : Projective (freeCover M) := by
  unfold freeCover; infer_instance

instance (M : ModuleCat.{u} R) [Module.Finite R M] : Epi (freeCoverπ M) := by
  rw [ModuleCat.epi_iff_surjective]
  exact (Module.Finite.exists_fin' R M).choose_spec.choose_spec

end FreeCover

/-! ### The syzygy tower -/

variable [IsNoetherianRing R]

/-- The kernel of a morphism out of a finite module is finite (over a Noetherian ring). -/
theorem finite_kernel {A B : ModuleCat.{u} R} (f : A ⟶ B) [Module.Finite R A] :
    Module.Finite R (kernel f : ModuleCat.{u} R) :=
  Module.Finite.of_injective (kernel.ι f).hom ((ModuleCat.mono_iff_injective _).1 inferInstance)

/-- The `n`-th syzygy module of the finite free resolution of `M`, packaged with its finiteness.
By convention `syzygyMod M 0 = M`, and `syzygyMod M (n+1) = ker (freeCoverπ (syzygyMod M n))`. -/
noncomputable def syzygyData (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∀ _n : ℕ, Σ' K : ModuleCat.{u} R, Module.Finite R K
  | 0 => ⟨M, ‹_›⟩
  | n + 1 =>
    letI := (syzygyData M n).2
    ⟨kernel (freeCoverπ (syzygyData M n).1), finite_kernel _⟩

/-- The `n`-th syzygy module `Ωⁿ M`. -/
noncomputable def syzygyMod (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) : ModuleCat.{u} R :=
  (syzygyData M n).1

instance (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) : Module.Finite R (syzygyMod M n) :=
  (syzygyData M n).2

@[simp] lemma syzygyMod_zero (M : ModuleCat.{u} R) [Module.Finite R M] : syzygyMod M 0 = M := rfl

/-- The `n`-th term of the resolution: the finite free cover of the `n`-th syzygy. -/
noncomputable abbrev Xobj (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) : ModuleCat.{u} R :=
  freeCover (syzygyMod M n)

/-- The cover map `Xₙ ↠ Ωⁿ M`. -/
noncomputable abbrev pmap (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    Xobj M n ⟶ syzygyMod M n :=
  freeCoverπ (syzygyMod M n)

lemma syzygyMod_succ (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    syzygyMod M (n + 1) = kernel (pmap M n) := rfl

/-- The differential `Xₙ₊₁ ⟶ Xₙ` of the resolution: cover of the next syzygy, followed by the
kernel inclusion `Ωⁿ⁺¹ M = ker(pₙ) ↪ Xₙ`. -/
noncomputable def d (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) : Xobj M (n + 1) ⟶ Xobj M n :=
  pmap M (n + 1) ≫ kernel.ι (pmap M n)

lemma dd (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) : d M (n + 1) ≫ d M n = 0 := by
  dsimp only [d]
  rw [Category.assoc, ← Category.assoc (kernel.ι (pmap M (n + 1))), kernel.condition, zero_comp,
    comp_zero]

/-! ### Exactness -/

lemma d_comp_p (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    d M n ≫ pmap M n = 0 := by
  dsimp only [d]; rw [Category.assoc, kernel.condition, comp_zero]

/-- The presentation `Xₙ₊₁ →(d) Xₙ →(pₙ) Ωⁿ M` is exact: the finite-cover analogue of
`CategoryTheory.exact_d_f`. -/
lemma pStep_exact (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    (ShortComplex.mk (d M n) (pmap M n) (d_comp_p M n)).Exact := by
  let α : ShortComplex.mk (d M n) (pmap M n) (d_comp_p M n) ⟶
      ShortComplex.kernelSequence (pmap M n) :=
    { τ₁ := pmap M (n + 1)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [d]
      comm₂₃ := by simp }
  haveI : Epi α.τ₁ := (inferInstance : Epi (pmap M (n + 1)))
  haveI : IsIso α.τ₂ := (inferInstance : IsIso (𝟙 (Xobj M n)))
  haveI : Mono α.τ₃ := (inferInstance : Mono (𝟙 (syzygyMod M n)))
  rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono α]
  exact ShortComplex.kernelSequence_exact _

/-- Exactness of the complex at `Xₙ₊₁`: `Xₙ₊₂ → Xₙ₊₁ → Xₙ`. -/
lemma exact_d_d (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    (ShortComplex.mk (d M (n + 1)) (d M n) (dd M n)).Exact := by
  let α : ShortComplex.mk (d M (n + 1)) (pmap M (n + 1)) (d_comp_p M (n + 1)) ⟶
      ShortComplex.mk (d M (n + 1)) (d M n) (dd M n) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := kernel.ι (pmap M n)
      comm₁₂ := by simp
      comm₂₃ := by simp [d] }
  haveI : Epi α.τ₁ := (inferInstance : Epi (𝟙 (Xobj M (n + 1 + 1))))
  haveI : IsIso α.τ₂ := (inferInstance : IsIso (𝟙 (Xobj M (n + 1))))
  haveI : Mono α.τ₃ := (inferInstance : Mono (kernel.ι (pmap M n)))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).mp (pStep_exact M (n + 1))

/-! ### The resolution -/

/-- The finite free chain complex `⋯ → X₂ → X₁ → X₀`. -/
noncomputable def cx (M : ModuleCat.{u} R) [Module.Finite R M] : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (Xobj M) (d M) (dd M)

instance (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) : Projective ((cx M).X n) :=
  inferInstanceAs (Projective (Xobj M n))

lemma cx_d (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    (cx M).d (n + 1) n = d M n := by
  simp [cx]

lemma cx_exactAt_succ (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    (cx M).ExactAt (n + 1) := by
  rw [(cx M).exactAt_iff' (n + 1 + 1) (n + 1) n (by simp) (by simp)]
  refine ShortComplex.exact_of_iso ?_ (exact_d_d M n)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [cx_d]) (by simp [cx_d])

/-- The finite free projective resolution of a finitely generated module `M` over a left-Noetherian
ring. Every term `Xobj M n` is a finite free `R`-module. -/
noncomputable def resolution (M : ModuleCat.{u} R) [Module.Finite R M] :
    ProjectiveResolution M where
  complex := cx M
  hasHomology := fun _ => inferInstance
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨pmap M 0, by
        rw [cx_d]; dsimp only [d]; rw [Category.assoc, kernel.condition, comp_zero]⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2 ⟨pStep_exact M 0, inferInstance⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp [cx_d]) (by simp)
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact cx_exactAt_succ M n
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

/-- **Existence of a finitely generated projective resolution.** A finitely generated module `M`
over a left-Noetherian ring `R` admits a projective resolution all of whose terms are finite free
`R`-modules (in particular `Module.Finite R`). -/
theorem exists_finite_projectiveResolution (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∃ P : ProjectiveResolution M, ∀ n, Module.Finite R (P.complex.X n) := by
  refine ⟨resolution M, fun n => ?_⟩
  change Module.Finite R (Xobj M n)
  infer_instance

end Etingof.FiniteProjectiveResolution
