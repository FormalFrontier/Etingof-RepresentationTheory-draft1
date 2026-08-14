/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Noetherian.Basic
import RepresentationTheory.Alignment.Attribute

set_option backward.isDefEq.respectTransparency false

/-!
# Finite projective resolutions

This module constructs a projective resolution with finite free terms for a finite module over a
Noetherian ring.
-/

universe u

open CategoryTheory Limits

namespace RepresentationTheory.AuxiliaryProjectiveResolution

variable {R : Type u} [Ring R]

/-! ### Finite free covers -/

section FreeCover

/-- A natural-number bound attached to a finite module. -/
noncomputable def auxiliaryFiniteModuleBound (M : ModuleCat.{u} R) [Module.Finite R M] : ℕ :=
  (Module.Finite.exists_fin' R M).choose

/-- An auxiliary module associated to a finite module. -/
noncomputable def auxiliaryProjectiveSource
    (M : ModuleCat.{u} R) [Module.Finite R M] : ModuleCat.{u} R :=
  ModuleCat.of R (Fin (auxiliaryFiniteModuleBound M) → R)

/-- The canonical morphism from the auxiliary projective source to the given module. -/
noncomputable def auxiliaryProjectiveSourceTo
    (M : ModuleCat.{u} R) [Module.Finite R M] : auxiliaryProjectiveSource M ⟶ M :=
  ModuleCat.ofHom (Module.Finite.exists_fin' R M).choose_spec.choose

/-- The auxiliary projective source of a finite module is finite. -/
instance auxiliaryProjectiveSource_finite
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    Module.Finite R (auxiliaryProjectiveSource M) := by
  unfold auxiliaryProjectiveSource ModuleCat.of; infer_instance

/-- The auxiliary projective source is projective. -/
instance auxiliaryProjectiveSource_projective
    (M : ModuleCat.{u} R) [Module.Finite R M] : Projective (auxiliaryProjectiveSource M) := by
  unfold auxiliaryProjectiveSource; infer_instance

/-- The morphism from the auxiliary projective source is an epimorphism. -/
instance auxiliaryProjectiveSourceTo_epi
    (M : ModuleCat.{u} R) [Module.Finite R M] : Epi (auxiliaryProjectiveSourceTo M) := by
  rw [ModuleCat.epi_iff_surjective]
  exact (Module.Finite.exists_fin' R M).choose_spec.choose_spec

end FreeCover

/-! ### The syzygy tower -/

variable [IsNoetherianRing R]

/-- The kernel of a morphism with finite source is finite over a Noetherian ring. -/
theorem finite_kernel {A B : ModuleCat.{u} R} (f : A ⟶ B) [Module.Finite R A] :
    Module.Finite R (kernel f : ModuleCat.{u} R) :=
  Module.Finite.of_injective (kernel.ι f).hom ((ModuleCat.mono_iff_injective _).1 inferInstance)

/-- An auxiliary definition whose formal expression is unavailable. -/
noncomputable def auxiliaryOpaqueDefinition (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∀ _n : ℕ, Σ' K : ModuleCat.{u} R, Module.Finite R K
  | 0 => ⟨M, ‹_›⟩
  | n + 1 =>
    letI := (auxiliaryOpaqueDefinition M n).2
    ⟨kernel (auxiliaryProjectiveSourceTo (auxiliaryOpaqueDefinition M n).1), finite_kernel _⟩

/-- The recursively indexed auxiliary module used in the resolution construction. -/
noncomputable def auxiliarySyzygy (M : ModuleCat.{u} R) [Module.Finite R M]
    (n : ℕ) : ModuleCat.{u} R :=
  (auxiliaryOpaqueDefinition M n).1

/-- Every displayed auxiliary syzygy is finite over the base ring. -/
instance auxiliarySyzygy_finite (M : ModuleCat.{u} R) [Module.Finite R M]
    (n : ℕ) : Module.Finite R (auxiliarySyzygy M n) :=
  (auxiliaryOpaqueDefinition M n).2

/-- The zeroth auxiliary syzygy is the original module. -/
@[simp] lemma auxiliarySyzygy_zero (M : ModuleCat.{u} R) [Module.Finite R M] :
    auxiliarySyzygy M 0 = M := rfl

/-- The module placed at a given degree in an auxiliary resolution construction. -/
noncomputable abbrev auxiliaryResolutionTerm
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) : ModuleCat.{u} R :=
  auxiliaryProjectiveSource (auxiliarySyzygy M n)

/-- The morphism from an auxiliary resolution term to the corresponding syzygy. -/
noncomputable abbrev auxiliaryResolutionMap
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    auxiliaryResolutionTerm M n ⟶ auxiliarySyzygy M n :=
  auxiliaryProjectiveSourceTo (auxiliarySyzygy M n)

/-- The next auxiliary syzygy is the kernel of the corresponding resolution map. -/
lemma auxiliarySyzygy_succ_eq_kernel (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    auxiliarySyzygy M (n + 1) = kernel (auxiliaryResolutionMap M n) := rfl

/-- The morphism between successive terms of the auxiliary resolution. -/
noncomputable def auxiliaryResolutionDifferential
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    auxiliaryResolutionTerm M (n + 1) ⟶ auxiliaryResolutionTerm M n :=
  auxiliaryResolutionMap M (n + 1) ≫ kernel.ι (auxiliaryResolutionMap M n)

/-- Two consecutive auxiliary resolution differentials compose to zero. -/
lemma auxiliaryResolutionDifferential_comp
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    auxiliaryResolutionDifferential M (n + 1) ≫ auxiliaryResolutionDifferential M n = 0 := by
  dsimp only [auxiliaryResolutionDifferential]
  rw [Category.assoc, ← Category.assoc (kernel.ι (auxiliaryResolutionMap M (n + 1))),
    kernel.condition, zero_comp, comp_zero]

/-! ### Exactness -/

/-- The composite of the indicated resolution differential and map is zero. -/
lemma auxiliaryResolutionDifferential_comp_auxiliaryResolutionMap
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    auxiliaryResolutionDifferential M n ≫ auxiliaryResolutionMap M n = 0 := by
  dsimp only [auxiliaryResolutionDifferential]; rw [Category.assoc, kernel.condition, comp_zero]

/-- The short complex connecting a resolution term and auxiliary syzygy is exact. -/
lemma auxiliaryResolutionShortComplex_exact
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    (ShortComplex.mk (auxiliaryResolutionDifferential M n) (auxiliaryResolutionMap M n)
      (auxiliaryResolutionDifferential_comp_auxiliaryResolutionMap M n)).Exact := by
  let α : ShortComplex.mk (auxiliaryResolutionDifferential M n) (auxiliaryResolutionMap M n)
      (auxiliaryResolutionDifferential_comp_auxiliaryResolutionMap M n) ⟶
      ShortComplex.kernelSequence (auxiliaryResolutionMap M n) :=
    { τ₁ := auxiliaryResolutionMap M (n + 1)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [auxiliaryResolutionDifferential]
      comm₂₃ := by simp }
  haveI : Epi α.τ₁ := (inferInstance : Epi (auxiliaryResolutionMap M (n + 1)))
  haveI : IsIso α.τ₂ := (inferInstance : IsIso (𝟙 (auxiliaryResolutionTerm M n)))
  haveI : Mono α.τ₃ := (inferInstance : Mono (𝟙 (auxiliarySyzygy M n)))
  rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono α]
  exact ShortComplex.kernelSequence_exact _

/-- The short complex formed by consecutive auxiliary resolution differentials is exact. -/
lemma auxiliaryResolutionDifferential_exact
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    (ShortComplex.mk (auxiliaryResolutionDifferential M (n + 1))
      (auxiliaryResolutionDifferential M n) (auxiliaryResolutionDifferential_comp M n)).Exact := by
  let α : ShortComplex.mk (auxiliaryResolutionDifferential M (n + 1))
      (auxiliaryResolutionMap M (n + 1))
      (auxiliaryResolutionDifferential_comp_auxiliaryResolutionMap M (n + 1)) ⟶
      ShortComplex.mk (auxiliaryResolutionDifferential M (n + 1))
        (auxiliaryResolutionDifferential M n) (auxiliaryResolutionDifferential_comp M n) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := kernel.ι (auxiliaryResolutionMap M n)
      comm₁₂ := by simp
      comm₂₃ := by simp [auxiliaryResolutionDifferential] }
  haveI : Epi α.τ₁ :=
    (inferInstance : Epi (𝟙 (auxiliaryResolutionTerm M (n + 1 + 1))))
  haveI : IsIso α.τ₂ :=
    (inferInstance : IsIso (𝟙 (auxiliaryResolutionTerm M (n + 1))))
  haveI : Mono α.τ₃ := (inferInstance : Mono (kernel.ι (auxiliaryResolutionMap M n)))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).mp
    (auxiliaryResolutionShortComplex_exact M (n + 1))

/-! ### The resolution -/

/-- An auxiliary chain complex associated to a finite module over a Noetherian ring. -/
noncomputable def auxiliaryResolutionComplex
    (M : ModuleCat.{u} R) [Module.Finite R M] : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (auxiliaryResolutionTerm M) (auxiliaryResolutionDifferential M)
    (auxiliaryResolutionDifferential_comp M)

/-- Each degree of the auxiliary resolution complex is projective. -/
instance auxiliaryResolutionComplex_projective
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    Projective ((auxiliaryResolutionComplex M).X n) :=
  inferInstanceAs (Projective (auxiliaryResolutionTerm M n))

/-- Identifies a differential of the auxiliary resolution complex with the displayed morphism. -/
lemma auxiliaryResolutionComplex_d
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    (auxiliaryResolutionComplex M).d (n + 1) n = auxiliaryResolutionDifferential M n := by
  simp [auxiliaryResolutionComplex]

/-- The auxiliary resolution complex is exact at each positive degree. -/
lemma auxiliaryResolutionComplex_exactAt_succ
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    (auxiliaryResolutionComplex M).ExactAt (n + 1) := by
  rw [(auxiliaryResolutionComplex M).exactAt_iff' (n + 1 + 1) (n + 1) n
    (by simp) (by simp)]
  refine ShortComplex.exact_of_iso ?_ (auxiliaryResolutionDifferential_exact M n)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [auxiliaryResolutionComplex_d]) (by simp [auxiliaryResolutionComplex_d])

/-- A projective resolution selected for a finite module over a Noetherian ring. -/
noncomputable def auxiliaryProjectiveResolution
    (M : ModuleCat.{u} R) [Module.Finite R M] : ProjectiveResolution M where
  complex := auxiliaryResolutionComplex M
  hasHomology := fun _ => inferInstance
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨auxiliaryResolutionMap M 0, by
        rw [auxiliaryResolutionComplex_d]; dsimp only [auxiliaryResolutionDifferential];
        rw [Category.assoc, kernel.condition, comp_zero]⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
          ⟨auxiliaryResolutionShortComplex_exact M 0, inferInstance⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp [auxiliaryResolutionComplex_d]) (by simp)
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact auxiliaryResolutionComplex_exactAt_succ M n
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

/-- A finite module over a Noetherian ring admits a projective resolution with finite terms. -/
@[source_ref "Chapter9/Problem9.4.2" (role := supporting)]
theorem exists_finite_projectiveResolution (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∃ P : ProjectiveResolution M, ∀ n, Module.Finite R (P.complex.X n) := by
  refine ⟨auxiliaryProjectiveResolution M, fun n => ?_⟩
  change Module.Finite R (auxiliaryResolutionTerm M n)
  infer_instance

end RepresentationTheory.AuxiliaryProjectiveResolution
