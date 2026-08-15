/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENCE.
Authors: mathlib-initiative
-/
import RepresentationTheory.Algebra.TensorProduct.ModuleCat
import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.ComplexShapeSigns
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

set_option backward.isDefEq.respectTransparency false

/-!
# Tensor products of projective resolutions

This module constructs the total tensor-product complex of two projective resolutions of left
modules and its auxiliary morphism to the tensor product concentrated in degree zero.
-/

open CategoryTheory Limits MonoidalCategory HomologicalComplex TensorProduct

namespace RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct

universe u

variable {k : Type u} [CommRing k]
variable {A₁ A₂ : Type u} [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]

attribute [local instance]
  RepresentationTheory.Algebra.TensorProduct.ModuleCat.moduleCarrier
  RepresentationTheory.Algebra.TensorProduct.ModuleCat.moduleCarrierAux
  RepresentationTheory.Algebra.TensorProduct.ModuleCat.isScalarTower
  RepresentationTheory.Algebra.TensorProduct.ModuleCat.isScalarTowerAux
  RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductModule

section ZeroMorphisms

/-- The displayed auxiliary two-variable map vanishes when its first morphism argument is zero. -/
theorem auxiliaryMap_zero_left {X X' : ModuleCat.{u} A₁} {Y Y' : ModuleCat.{u} A₂}
    (g : Y ⟶ Y') :
    RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductLinearMap
      k (0 : X ⟶ X') g = 0 := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m₁ m₂ =>
    rw [RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductLinearMap_tmul,
      ModuleCat.hom_zero, LinearMap.zero_apply, zero_tmul, LinearMap.zero_apply]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- This auxiliary map is zero when its first morphism input is zero. -/
theorem auxiliaryMapToSingle_zero_left {X X' : ModuleCat.{u} A₁} {Y Y' : ModuleCat.{u} A₂}
    (g : Y ⟶ Y') :
    RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductMap
      k (0 : X ⟶ X') g = 0 := by
  change ModuleCat.ofHom
    (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductLinearMap
      k (0 : X ⟶ X') g) = 0
  rw [auxiliaryMap_zero_left, ModuleCat.ofHom_zero]

/-- The displayed auxiliary two-variable map vanishes when its second morphism argument is zero. -/
theorem auxiliaryMap_zero_right {X X' : ModuleCat.{u} A₁} {Y Y' : ModuleCat.{u} A₂}
    (f : X ⟶ X') :
    RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductLinearMap
      k f (0 : Y ⟶ Y') = 0 := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m₁ m₂ =>
    rw [RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductLinearMap_tmul,
      ModuleCat.hom_zero, LinearMap.zero_apply, tmul_zero, LinearMap.zero_apply]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- This auxiliary map is zero when its second morphism input is zero. -/
theorem auxiliaryMapToSingle_zero_right {X X' : ModuleCat.{u} A₁} {Y Y' : ModuleCat.{u} A₂}
    (f : X ⟶ X') :
    RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductMap
      k f (0 : Y ⟶ Y') = 0 := by
  change ModuleCat.ofHom
    (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductLinearMap
      k f (0 : Y ⟶ Y')) = 0
  rw [auxiliaryMap_zero_right, ModuleCat.ofHom_zero]

/-- The indicated functor sends zero morphisms to zero morphisms. -/
instance auxiliaryFunctor_preservesZeroMorphisms :
    (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor
      k A₁ A₂).PreservesZeroMorphisms where
  map_zero X X' := by
    apply NatTrans.ext
    funext Y
    change RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductMap
      k (0 : X ⟶ X') (𝟙 Y) = 0
    exact auxiliaryMapToSingle_zero_left (𝟙 Y)

/-- Every object image under the indicated functor has the zero-morphism preservation property. -/
instance auxiliaryFunctor_obj_preservesZeroMorphisms (X : ModuleCat.{u} A₁) :
    ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor
      k A₁ A₂).obj X).PreservesZeroMorphisms where
  map_zero Y Y' := by
    change RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductMap
      k (𝟙 X) (0 : Y ⟶ Y') = 0
    exact auxiliaryMapToSingle_zero_right (𝟙 X)

/-- For every natural number, the fibre of the downward complex shape over that index is finite. -/
instance finite_preimage_down (n : ℕ) :
    Finite (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) ⁻¹' {n}) := by
  refine Finite.of_injective (fun ⟨⟨i₁, i₂⟩, (hi : i₁ + i₂ = n)⟩ =>
    ((⟨i₁, by omega⟩, ⟨i₂, by omega⟩) : Fin (n + 1) × Fin (n + 1))) ?_
  rintro ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ h
  simpa using h

end ZeroMorphisms

variable {M₁ : ModuleCat.{u} A₁} {M₂ : ModuleCat.{u} A₂}

/-- Builds the chain complex over the tensor-product ring associated to two projective
resolutions. -/
noncomputable abbrev tensorProduct
    (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂) :
    ChainComplex (ModuleCat.{u} (A₁ ⊗[k] A₂)) ℕ :=
  HomologicalComplex.mapBifunctor P₁.complex P₂.complex
    (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂)
    (ComplexShape.down ℕ)

/-- An auxiliary morphism from degree zero of the displayed tensor-product complex to its specified
target. -/
noncomputable abbrev auxiliaryMap
    (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂) :
    (tensorProduct P₁ P₂).X 0 ⟶
      RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProduct k A₁ A₂ M₁ M₂ :=
  HomologicalComplex.mapBifunctorDesc (j := 0) fun i₁ i₂ h =>
    match i₁, i₂, h with
    | 0, 0, _ =>
        ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor
            k A₁ A₂).map
            ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1).app
          (P₂.complex.X 0) ≫
        ((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor
          k A₁ A₂).obj M₁).map
          ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).1
    | (_ + 1), _, h => absurd h (by simp)
    | 0, (_ + 1), h => absurd h (by simp)

/-- The differential from degree one to degree zero composed with the auxiliary morphism is zero. -/
theorem d_auxiliaryMap (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂) :
    (tensorProduct (k := k) P₁ P₂).d 1 0 ≫ auxiliaryMap (k := k) P₁ P₂ = 0 := by
  have hd₁ : P₁.complex.d 1 0 ≫ ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1 = 0 :=
    ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).2
  have hd₂ : P₂.complex.d 1 0 ≫ ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).1 = 0 :=
    ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).2
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i₁ i₂ h
  rw [comp_zero]
  simp only [HomologicalComplex.mapBifunctor.d_eq, Preadditive.add_comp,
    Preadditive.comp_add, HomologicalComplex.mapBifunctor.ι_D₁_assoc,
    HomologicalComplex.mapBifunctor.ι_D₂_assoc]
  have hi : i₁ + i₂ = 1 := h
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (i₁ = 1 ∧ i₂ = 0) ∨ (i₁ = 0 ∧ i₂ = 1) := by omega
  · rw [HomologicalComplex.mapBifunctor.d₂_eq_zero (K₁ := P₁.complex) (K₂ := P₂.complex)
        (F := RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂)
        (c := ComplexShape.down ℕ) (i₁ := 1) (i₂ := 0) (j := 0) (by simp),
      HomologicalComplex.mapBifunctor.d₁_eq (K₁ := P₁.complex) (K₂ := P₂.complex)
        (F := RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂)
        (c := ComplexShape.down ℕ) (i₁ := 1) (i₁' := 0) (i₂ := 0) (j := 0)
        (h := by simp) (h' := by simp)]
    rw [zero_comp, add_zero,
      show ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) (1, 0) = 1 from rfl, one_smul, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc, ← NatTrans.comp_app_assoc, ← Functor.map_comp, hd₁]
    simp
  · rw [HomologicalComplex.mapBifunctor.d₁_eq_zero (K₁ := P₁.complex) (K₂ := P₂.complex)
        (F := RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂)
        (c := ComplexShape.down ℕ) (i₁ := 0) (i₂ := 1) (j := 0) (by simp),
      HomologicalComplex.mapBifunctor.d₂_eq (K₁ := P₁.complex) (K₂ := P₂.complex)
        (F := RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂)
        (c := ComplexShape.down ℕ) (i₁ := 0) (i₂ := 1) (i₂' := 0) (j := 0)
        (h := by simp) (h' := by simp)]
    rw [zero_comp, zero_add,
      show ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) (0, 1) = 1 from by simp [ComplexShape.ε₂, ComplexShape.ε],
      one_smul, Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
    dsimp only
    rw [((RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).map
        ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1).naturality_assoc,
      ← Functor.map_comp, hd₂]
    simp

/-- Packages an auxiliary morphism from the displayed complex as a map into a complex concentrated
in degree zero. -/
noncomputable def auxiliaryToSingle
    (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂) :
    tensorProduct P₁ P₂ ⟶
      (ChainComplex.single₀ (ModuleCat.{u} (A₁ ⊗[k] A₂))).obj
        (RepresentationTheory.Algebra.TensorProduct.ModuleCat.tensorProduct k A₁ A₂ M₁ M₂) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨auxiliaryMap P₁ P₂, d_auxiliaryMap P₁ P₂⟩

end RepresentationTheory.HomologicalAlgebra.ProjectiveResolution.TensorProduct
