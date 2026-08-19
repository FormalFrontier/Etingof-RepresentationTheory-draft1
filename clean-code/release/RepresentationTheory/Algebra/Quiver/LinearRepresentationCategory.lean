/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: Kim Morrison
-/

import RepresentationTheory.CategoryTheory.QuiverLinearMaps
import Mathlib.CategoryTheory.Category.Basic

/-! # Category of quiver linear diagrams -/

namespace RepresentationTheory.CategoryTheory.QuiverLinearMaps

open RepresentationTheory.CategoryTheory.QuiverLinearDiagrams

/-- Two representation morphisms are equal when all of their vertex components are equal. -/
@[ext] theorem AuxiliaryQuiverLinearMapData.ext
    {k : Type*} {Q : Type*} [CommSemiring k] [Quiver Q]
    {ρ₁ ρ₂ : AuxiliaryQuiverModuleData k Q}
    {f g : AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂} (h : ∀ v, f.app v = g.app v) : f = g := by
  cases f with
  | mk fa fn => cases g with
    | mk ga gn => have : fa = ga := funext h; subst this; rfl

/-- The identity morphism of a linear quiver representation. -/
def AuxiliaryQuiverLinearMapData.id {k : Type*} {Q : Type*} [CommSemiring k] [Quiver Q]
    (ρ : AuxiliaryQuiverModuleData k Q) : AuxiliaryQuiverLinearMapData k Q ρ ρ where
  app _ := LinearMap.id
  naturality _ _ := rfl

/-- Composition of morphisms between linear quiver representations. -/
def AuxiliaryQuiverLinearMapData.comp {k : Type*} {Q : Type*} [CommSemiring k] [Quiver Q]
    {ρ₁ ρ₂ ρ₃ : AuxiliaryQuiverModuleData k Q}
    (f : AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂)
    (g : AuxiliaryQuiverLinearMapData k Q ρ₂ ρ₃) :
    AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₃ where
  app v := (g.app v).comp (f.app v)
  naturality e x := by
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [f.naturality e x, g.naturality e (f.app _ x)]

/-- Each component of the identity representation morphism is the identity linear map. -/
@[simp] theorem AuxiliaryQuiverLinearMapData.id_apply {k : Type*} {Q : Type*} [CommSemiring k]
    [Quiver Q] (ρ : AuxiliaryQuiverModuleData k Q) (v : Q) :
    (AuxiliaryQuiverLinearMapData.id ρ).app v = LinearMap.id := rfl

/-- The component of a composite representation morphism is the composite of its components. -/
@[simp] theorem AuxiliaryQuiverLinearMapData.comp_apply {k : Type*} {Q : Type*} [CommSemiring k]
    [Quiver Q] {ρ₁ ρ₂ ρ₃ : AuxiliaryQuiverModuleData k Q}
    (f : AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂)
    (g : AuxiliaryQuiverLinearMapData k Q ρ₂ ρ₃) (v : Q) :
    (f.comp g).app v = (g.app v).comp (f.app v) := rfl

end RepresentationTheory.CategoryTheory.QuiverLinearMaps

namespace RepresentationTheory.CategoryTheory.QuiverLinearDiagrams

open RepresentationTheory.CategoryTheory.QuiverLinearMaps

/-- The category structure on linear representations of a quiver over a commutative semiring. -/
instance AuxiliaryQuiverModuleData.category {k : Type*} [CommSemiring k] {Q : Type*}
    [Quiver Q] : CategoryTheory.Category (AuxiliaryQuiverModuleData k Q) where
  Hom ρ₁ ρ₂ := AuxiliaryQuiverLinearMapData k Q ρ₁ ρ₂
  id ρ := AuxiliaryQuiverLinearMapData.id ρ
  comp f g := AuxiliaryQuiverLinearMapData.comp f g
  id_comp _ := by ext v; simp
  comp_id _ := by ext v; simp
  assoc _ _ _ := by ext v; simp

/-- The vertex component of the identity morphism is the identity linear map. -/
@[simp] theorem AuxiliaryQuiverModuleData.id_component {k : Type*} [CommSemiring k] {Q : Type*}
    [Quiver Q] (ρ : AuxiliaryQuiverModuleData k Q) (v : Q) :
    AuxiliaryQuiverLinearMapData.app (CategoryTheory.CategoryStruct.id ρ) v = LinearMap.id := rfl

/-- The vertex component of a composite morphism is the composite of the corresponding linear maps. -/
@[simp] theorem AuxiliaryQuiverModuleData.comp_component {k : Type*} [CommSemiring k] {Q : Type*}
    [Quiver Q] {ρ₁ ρ₂ ρ₃ : AuxiliaryQuiverModuleData k Q} (f : ρ₁ ⟶ ρ₂) (g : ρ₂ ⟶ ρ₃)
    (v : Q) :
    AuxiliaryQuiverLinearMapData.app (CategoryTheory.CategoryStruct.comp f g) v = (g.app v).comp (f.app v) := rfl

end RepresentationTheory.CategoryTheory.QuiverLinearDiagrams
