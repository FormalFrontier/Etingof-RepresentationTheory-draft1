/-
Copyright (c) 2026 FormalFrontier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: FormalFrontier
-/
import RepresentationTheory.CategoryTheory.ProjectiveEpiProperties
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Regular module property

This module records a projectivity and separator property of the regular module.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace RepresentationTheory.RegularModuleProperty

/-- The regular module of a ring satisfies the indicated module property. -/
theorem regularModuleProperty (R : Type u) [Ring R] :
    RepresentationTheory.CategoryTheory.ProjectiveEpiProperties.IsProjectiveEpiSigmaDesc
      (ModuleCat.of R R) := by
  refine ⟨inferInstance, ?_⟩
  rw [isSeparator_def]
  intro X Y f g hfg
  apply ModuleCat.hom_ext
  ext x
  have h := hfg (ModuleCat.ofHom (LinearMap.toSpanSingleton R X x))
  simpa using congrArg (fun φ => ModuleCat.Hom.hom φ (1 : R)) h

end RepresentationTheory.RegularModuleProperty
