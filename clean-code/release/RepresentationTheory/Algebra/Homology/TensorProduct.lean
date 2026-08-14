import RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat
import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.ComplexShapeSigns
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits MonoidalCategory HomologicalComplex TensorProduct MulOpposite

namespace RepresentationTheory.Algebra.Homology.TensorProduct

universe u

variable {k : Type u} [CommRing k]
variable {A₁ A₂ : Type u} [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]

section ZeroMorphisms

/-- Provides the base-ring module structure on the carrier of the first right-module object. -/
noncomputable local instance leftFactorCarrierModule (X : ModuleCat.{u} A₁ᵐᵒᵖ) : Module k X :=
  Module.compHom X (algebraMap k A₁ᵐᵒᵖ)

/-- Provides the base-ring module structure on the carrier of the second right-module object. -/
noncomputable local instance rightFactorCarrierModule (Y : ModuleCat.{u} A₂ᵐᵒᵖ) : Module k Y :=
  Module.compHom Y (algebraMap k A₂ᵐᵒᵖ)

/-- The carrier of the first right-module object forms a scalar tower over the base ring and opposite algebra. -/
local instance leftFactor_isScalarTower (X : ModuleCat.{u} A₁ᵐᵒᵖ) : IsScalarTower k A₁ᵐᵒᵖ X :=
  { smul_assoc := fun a b x => by rw [Algebra.smul_def]; exact mul_smul _ _ _ }

/-- The carrier of the second right-module object forms a scalar tower over the base ring and opposite algebra. -/
local instance rightFactor_isScalarTower (Y : ModuleCat.{u} A₂ᵐᵒᵖ) : IsScalarTower k A₂ᵐᵒᵖ Y :=
  { smul_assoc := fun a b x => by rw [Algebra.smul_def]; exact mul_smul _ _ _ }

/-- Provides a module structure over the opposite tensor product on the tensor product of the two carriers. -/
noncomputable local instance tensorProductModule (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    Module (A₁ ⊗[k] A₂)ᵐᵒᵖ (X ⊗[k] Y) :=
  RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductModule k A₁ A₂ X Y

/-- Mapping a zero morphism in the first argument and any morphism in the second argument gives zero. -/
theorem bimapZeroLeft {X X' : ModuleCat.{u} A₁ᵐᵒᵖ} {Y Y' : ModuleCat.{u} A₂ᵐᵒᵖ}
    (g : Y ⟶ Y') :
    RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductLinearMap k (0 : X ⟶ X') g = 0 := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m₁ m₂ =>
    rw [RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductLinearMap_tmul,
      ModuleCat.hom_zero, LinearMap.zero_apply, zero_tmul, LinearMap.zero_apply]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The displayed binary morphism construction sends a zero first argument to zero. -/
theorem bimapToZeroLeft {X X' : ModuleCat.{u} A₁ᵐᵒᵖ} {Y Y' : ModuleCat.{u} A₂ᵐᵒᵖ}
    (g : Y ⟶ Y') :
    RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductHom k (0 : X ⟶ X') g = 0 := by
  change ModuleCat.ofHom
    (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductLinearMap k
      (0 : X ⟶ X') g) = 0
  rw [bimapZeroLeft, ModuleCat.ofHom_zero]

/-- Mapping any morphism in the first argument and a zero morphism in the second argument gives zero. -/
theorem bimapZeroRight {X X' : ModuleCat.{u} A₁ᵐᵒᵖ} {Y Y' : ModuleCat.{u} A₂ᵐᵒᵖ}
    (f : X ⟶ X') :
    RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductLinearMap k f (0 : Y ⟶ Y') = 0 := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m₁ m₂ =>
    rw [RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductLinearMap_tmul,
      ModuleCat.hom_zero, LinearMap.zero_apply, tmul_zero, LinearMap.zero_apply]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The displayed binary morphism construction sends a zero second argument to zero. -/
theorem bimapToZeroRight {X X' : ModuleCat.{u} A₁ᵐᵒᵖ} {Y Y' : ModuleCat.{u} A₂ᵐᵒᵖ}
    (f : X ⟶ X') :
    RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductHom k f (0 : Y ⟶ Y') = 0 := by
  change ModuleCat.ofHom
    (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductLinearMap k f
      (0 : Y ⟶ Y')) = 0
  rw [bimapZeroRight, ModuleCat.ofHom_zero]

/-- The displayed tensor-product functor preserves zero morphisms. -/
instance tensorProductFunctor_preservesZeroMorphisms :
    (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).PreservesZeroMorphisms where
  map_zero X X' := by
    apply NatTrans.ext
    funext Y
    change RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductHom k
      (0 : X ⟶ X') (𝟙 Y) = 0
    exact bimapToZeroLeft (𝟙 Y)

/-- For every first input object, the resulting functor preserves zero morphisms. -/
instance tensorProductFunctor_obj_preservesZeroMorphisms (X : ModuleCat.{u} A₁ᵐᵒᵖ) :
    ((RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).obj X).PreservesZeroMorphisms where
  map_zero Y Y' := by
    change RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductHom k
      (𝟙 X) (0 : Y ⟶ Y') = 0
    exact bimapToZeroRight (𝟙 X)

/-- Each fibre of the downward complex shape over a natural-number index is finite. -/
instance finite_preimage_down (n : ℕ) :
    Finite (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) ⁻¹' {n}) := by
  refine Finite.of_injective (fun ⟨⟨i₁, i₂⟩, (hi : i₁ + i₂ = n)⟩ =>
    ((⟨i₁, by omega⟩, ⟨i₂, by omega⟩) : Fin (n + 1) × Fin (n + 1))) ?_
  rintro ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ h
  simpa using h

end ZeroMorphisms

variable {M₁ : ModuleCat.{u} A₁ᵐᵒᵖ} {M₂ : ModuleCat.{u} A₂ᵐᵒᵖ}

/-- Constructs a chain complex of modules over the opposite tensor product from the two given inputs. -/
noncomputable abbrev tensorProductComplex
    (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂) :
    ChainComplex (ModuleCat.{u} (A₁ ⊗[k] A₂)ᵐᵒᵖ) ℕ :=
  HomologicalComplex.mapBifunctor P₁.complex P₂.complex
    (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂)
    (ComplexShape.down ℕ)

/-- The morphism from the degree-zero term of the displayed complex to the target object. -/
noncomputable abbrev zeroComponentToTarget
    (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂) :
    (tensorProductComplex P₁ P₂).X 0 ⟶
      RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductObject k A₁ A₂ M₁ M₂ :=
  HomologicalComplex.mapBifunctorDesc (j := 0) fun i₁ i₂ h =>
    match i₁, i₂, h with
    | 0, 0, _ =>
        ((RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).map
          ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1).app
          (P₂.complex.X 0) ≫
        ((RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).obj M₁).map
          ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).1
    | (_ + 1), _, h => absurd h (by simp)
    | 0, (_ + 1), h => absurd h (by simp)

/-- The differential from degree one to degree zero composed with the displayed degree-zero morphism is zero. -/
theorem dOneZero_comp_zeroComponentToTarget (P₁ : ProjectiveResolution M₁)
    (P₂ : ProjectiveResolution M₂) :
    (tensorProductComplex (k := k) P₁ P₂).d 1 0 ≫
      zeroComponentToTarget (k := k) P₁ P₂ = 0 := by
  have hd₁ : P₁.complex.d 1 0 ≫ ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1 = 0 :=
    ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).2
  have hd₂ : P₂.complex.d 1 0 ≫ ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).1 = 0 :=
    ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).2
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i₁ i₂ h
  rw [comp_zero]
  simp only [HomologicalComplex.mapBifunctor.d_eq, Preadditive.add_comp, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁_assoc, HomologicalComplex.mapBifunctor.ι_D₂_assoc]
  have hi : i₁ + i₂ = 1 := h
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (i₁ = 1 ∧ i₂ = 0) ∨ (i₁ = 0 ∧ i₂ = 1) := by omega
  · rw [HomologicalComplex.mapBifunctor.d₂_eq_zero (K₁ := P₁.complex) (K₂ := P₂.complex)
        (F := RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂)
        (c := ComplexShape.down ℕ) (i₁ := 1) (i₂ := 0) (j := 0)
        (by simp),
      HomologicalComplex.mapBifunctor.d₁_eq (K₁ := P₁.complex) (K₂ := P₂.complex)
        (F := RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂)
        (c := ComplexShape.down ℕ) (i₁ := 1) (i₁' := 0) (i₂ := 0)
        (j := 0) (h := by simp) (h' := by simp)]
    rw [zero_comp, add_zero,
      show ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) (1, 0) = 1 from rfl, one_smul, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc, ← NatTrans.comp_app_assoc, ← Functor.map_comp, hd₁]
    simp
  · rw [HomologicalComplex.mapBifunctor.d₁_eq_zero (K₁ := P₁.complex) (K₂ := P₂.complex)
        (F := RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂)
        (c := ComplexShape.down ℕ) (i₁ := 0) (i₂ := 1) (j := 0)
        (by simp),
      HomologicalComplex.mapBifunctor.d₂_eq (K₁ := P₁.complex) (K₂ := P₂.complex)
        (F := RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂)
        (c := ComplexShape.down ℕ) (i₁ := 0) (i₂ := 1) (i₂' := 0)
        (j := 0) (h := by simp) (h' := by simp)]
    rw [zero_comp, zero_add,
      show ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) (0, 1) = 1 from by simp [ComplexShape.ε₂, ComplexShape.ε],
      one_smul, Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
    dsimp only
    rw [((RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductFunctor k A₁ A₂).map
      ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1).naturality_assoc,
      ← Functor.map_comp, hd₂]
    simp

/-- Defines a morphism from the displayed chain complex to the complex concentrated in degree zero. -/
noncomputable def complexToSingleZero
    (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂) :
    tensorProductComplex P₁ P₂ ⟶
      (ChainComplex.single₀ (ModuleCat.{u} (A₁ ⊗[k] A₂)ᵐᵒᵖ)).obj
        (RepresentationTheory.Algebra.Algebra.TensorProduct.ModuleCat.tensorProductObject k A₁ A₂ M₁ M₂) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨zeroComponentToTarget P₁ P₂, dOneZero_comp_zeroComponentToTarget P₁ P₂⟩

end RepresentationTheory.Algebra.Homology.TensorProduct
