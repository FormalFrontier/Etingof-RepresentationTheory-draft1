/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/

import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Projective-resolution short complexes
-/

set_option backward.isDefEq.respectTransparency false

universe v u

open CategoryTheory Limits

namespace RepresentationTheory.CategoryTheory.Abelian.ObjectData.AbelianCategoryObjectData

variable {C : Type u} [Category.{v} C] [Abelian C] {M : C} (P : ProjectiveResolution M)

/-- Auxiliary data associated to a stage of a projective resolution. -/
structure StageData (n : ℕ) where
  /-- The object associated to the given stage data. -/
  target : C
  /-- The morphism from the resolution component to the associated target object. -/
  to_target : P.complex.X n ⟶ target
  /-- The displayed resolution differential composed with the attached morphism is zero. -/
  d_comp_to_target : P.complex.d (n + 1) n ≫ to_target = 0
  /-- The morphism attached to this stage data is an epimorphism. -/
  epi_to_target : Epi to_target
  /-- The short complex formed by the displayed differential and attached morphism is exact. -/
  exact : (ShortComplex.mk (P.complex.d (n + 1) n) to_target d_comp_to_target).Exact

namespace StageData

variable {P}

/-- Advances the given stage data to the next natural-number index. -/
noncomputable def next {n : ℕ} (s : StageData P n) : StageData P (n + 1) where
  target := kernel s.to_target
  to_target := kernel.lift s.to_target (P.complex.d (n + 1) n) s.d_comp_to_target
  d_comp_to_target := by
    rw [← cancel_mono (kernel.ι s.to_target), zero_comp, Category.assoc, kernel.lift_ι]
    exact P.complex.d_comp_d _ _ _
  epi_to_target := s.exact.epi_kernelLift
  exact := by
    refine (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      (S₁ := ShortComplex.mk (P.complex.d (n + 1 + 1) (n + 1))
        (kernel.lift s.to_target (P.complex.d (n + 1) n) s.d_comp_to_target)
        (by rw [← cancel_mono (kernel.ι s.to_target), zero_comp, Category.assoc, kernel.lift_ι]
            exact P.complex.d_comp_d _ _ _))
      (S₂ := ShortComplex.mk (P.complex.d (n + 1 + 1) (n + 1)) (P.complex.d (n + 1) n)
        (P.complex.d_comp_d _ _ _))
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := kernel.ι s.to_target
        comm₂₃ := by simp }).mpr (P.exact_succ n)

end StageData

/-- Constructs auxiliary stage data from a projective resolution and an index. -/
noncomputable def stage_data : ∀ n, StageData P n
  | 0 =>
    { target := M
      to_target := P.π.f 0
      d_comp_to_target := P.complex_d_comp_π_f_zero
      epi_to_target := inferInstance
      exact := ShortComplex.exact_of_g_is_cokernel _ P.isColimitCokernelCofork }
  | n + 1 => (stage_data n).next

/-- The object associated to a projective resolution at the specified stage. -/
noncomputable def stage_object (n : ℕ) : C := (stage_data P n).target

/-- The object associated to the zero stage is the resolved object. -/
@[simp] lemma stage_object_zero : stage_object P 0 = M := rfl

/-- The short complex associated to a projective resolution and a stage. -/
noncomputable def stage_short_complex (n : ℕ) : ShortComplex C :=
  ShortComplex.kernelSequence (stage_data P n).to_target

/-- Identifies the middle object of the associated short complex with the resolution component. -/
@[simp] lemma stage_short_complex_X2 (n : ℕ) :
    (stage_short_complex P n).X₂ = P.complex.X n := rfl

/-- Identifies the third object of the associated short complex. -/
@[simp] lemma stage_short_complex_X3 (n : ℕ) :
    (stage_short_complex P n).X₃ = stage_object P n := rfl

/-- Identifies the first object of the associated short complex. -/
@[simp] lemma stage_short_complex_X1 (n : ℕ) :
    (stage_short_complex P n).X₁ = stage_object P (n + 1) := rfl

/-- The middle object of the associated short complex is projective. -/
instance stage_short_complex_X2_projective (n : ℕ) : Projective (stage_short_complex P n).X₂ := by
  rw [stage_short_complex_X2]; exact P.projective n

/-- The associated short complex is short exact. -/
lemma stage_short_complex_short_exact (n : ℕ) : (stage_short_complex P n).ShortExact := by
  haveI hp : Epi (stage_data P n).to_target := (stage_data P n).epi_to_target
  change (ShortComplex.kernelSequence (stage_data P n).to_target).ShortExact
  refine ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact _) ?_ hp
  exact (inferInstance : Mono (kernel.ι (stage_data P n).to_target))

end RepresentationTheory.CategoryTheory.Abelian.ObjectData.AbelianCategoryObjectData
