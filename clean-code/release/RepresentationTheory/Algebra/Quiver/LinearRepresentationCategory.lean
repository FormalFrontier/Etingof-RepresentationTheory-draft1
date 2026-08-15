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
@[ext] theorem QuiverLinearHom.ext
    {k : Type*} {Q : Type*} [CommSemiring k] [Quiver Q]
    {ρ₁ ρ₂ : QuiverLinearDiagram k Q}
    {f g : QuiverLinearHom k Q ρ₁ ρ₂} (h : ∀ v, f.app v = g.app v) : f = g := by
  cases f with
  | mk fa fn => cases g with
    | mk ga gn => have : fa = ga := funext h; subst this; rfl

/-- The identity morphism of a linear quiver representation. -/
def QuiverLinearHom.id {k : Type*} {Q : Type*} [CommSemiring k] [Quiver Q]
    (ρ : QuiverLinearDiagram k Q) : QuiverLinearHom k Q ρ ρ where
  app _ := LinearMap.id
  naturality _ _ := rfl

/-- Composition of morphisms between linear quiver representations. -/
def QuiverLinearHom.comp {k : Type*} {Q : Type*} [CommSemiring k] [Quiver Q]
    {ρ₁ ρ₂ ρ₃ : QuiverLinearDiagram k Q}
    (f : QuiverLinearHom k Q ρ₁ ρ₂)
    (g : QuiverLinearHom k Q ρ₂ ρ₃) :
    QuiverLinearHom k Q ρ₁ ρ₃ where
  app v := (g.app v).comp (f.app v)
  naturality e x := by
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [f.naturality e x, g.naturality e (f.app _ x)]

/-- Each component of the identity representation morphism is the identity linear map. -/
@[simp] theorem QuiverLinearHom.id_apply {k : Type*} {Q : Type*} [CommSemiring k]
    [Quiver Q] (ρ : QuiverLinearDiagram k Q) (v : Q) :
    (QuiverLinearHom.id ρ).app v = LinearMap.id := rfl

/-- The component of a composite representation morphism is the composite of its components. -/
@[simp] theorem QuiverLinearHom.comp_apply {k : Type*} {Q : Type*} [CommSemiring k]
    [Quiver Q] {ρ₁ ρ₂ ρ₃ : QuiverLinearDiagram k Q}
    (f : QuiverLinearHom k Q ρ₁ ρ₂)
    (g : QuiverLinearHom k Q ρ₂ ρ₃) (v : Q) :
    (f.comp g).app v = (g.app v).comp (f.app v) := rfl

end RepresentationTheory.CategoryTheory.QuiverLinearMaps

namespace RepresentationTheory.CategoryTheory.QuiverLinearDiagrams

open RepresentationTheory.CategoryTheory.QuiverLinearMaps

/-- The category structure on linear representations of a quiver over a commutative semiring. -/
instance QuiverLinearDiagram.category {k : Type*} [CommSemiring k] {Q : Type*}
    [Quiver Q] : CategoryTheory.Category (QuiverLinearDiagram k Q) where
  Hom ρ₁ ρ₂ := QuiverLinearHom k Q ρ₁ ρ₂
  id ρ := QuiverLinearHom.id ρ
  comp f g := QuiverLinearHom.comp f g
  id_comp _ := by ext v; simp
  comp_id _ := by ext v; simp
  assoc _ _ _ := by ext v; simp

/-- The vertex component of the identity morphism is the identity linear map. -/
@[simp] theorem QuiverLinearDiagram.id_component {k : Type*} [CommSemiring k] {Q : Type*}
    [Quiver Q] (ρ : QuiverLinearDiagram k Q) (v : Q) :
    QuiverLinearHom.app (CategoryTheory.CategoryStruct.id ρ) v = LinearMap.id := rfl

/-- The vertex component of a composite morphism is the composite of the corresponding linear maps. -/
@[simp] theorem QuiverLinearDiagram.comp_component {k : Type*} [CommSemiring k] {Q : Type*}
    [Quiver Q] {ρ₁ ρ₂ ρ₃ : QuiverLinearDiagram k Q} (f : ρ₁ ⟶ ρ₂) (g : ρ₂ ⟶ ρ₃)
    (v : Q) :
    QuiverLinearHom.app (CategoryTheory.CategoryStruct.comp f g) v = (g.app v).comp (f.app v) := rfl

end RepresentationTheory.CategoryTheory.QuiverLinearDiagrams
