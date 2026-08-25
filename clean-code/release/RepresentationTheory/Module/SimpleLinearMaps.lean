/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.RingTheory.SimpleModule.Basic
import RepresentationTheory.Alignment.Attribute

/-! # Linear maps between simple modules -/

namespace RepresentationTheory.Module.SimpleLinearMaps

/-- A nonzero linear map out of a simple module is injective. -/
@[source_ref "Chapter2/Proposition2.3.9" (role := primary)]
theorem linearMap_injective_of_ne_zero_from_simple
    {R : Type*} [Ring R]
    {V₁ : Type*} [AddCommGroup V₁] [Module R V₁] [IsSimpleModule R V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module R V₂]
    (φ : V₁ →ₗ[R] V₂) (hφ : φ ≠ 0) : Function.Injective φ :=
  LinearMap.injective_of_ne_zero hφ

/-- A nonzero linear map into a simple module is surjective. -/
@[source_ref "Chapter2/Proposition2.3.9" (role := primary)]
theorem linearMap_surjective_of_ne_zero_to_simple
    {R : Type*} [Ring R]
    {V₁ : Type*} [AddCommGroup V₁] [Module R V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module R V₂] [IsSimpleModule R V₂]
    (φ : V₁ →ₗ[R] V₂) (hφ : φ ≠ 0) : Function.Surjective φ :=
  LinearMap.surjective_of_ne_zero hφ

/-- A nonzero linear map between simple modules is bijective. -/
@[source_ref "Chapter2/Proposition2.3.9" (role := primary)]
theorem linearMap_bijective_of_ne_zero_between_simple
    {R : Type*} [Ring R]
    {V₁ : Type*} [AddCommGroup V₁] [Module R V₁] [IsSimpleModule R V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module R V₂] [IsSimpleModule R V₂]
    (φ : V₁ →ₗ[R] V₂) (hφ : φ ≠ 0) : Function.Bijective φ :=
  ⟨linearMap_injective_of_ne_zero_from_simple φ hφ,
    linearMap_surjective_of_ne_zero_to_simple φ hφ⟩

end RepresentationTheory.Module.SimpleLinearMaps
