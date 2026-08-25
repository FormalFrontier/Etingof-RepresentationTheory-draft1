import EtingofRepresentationTheory.Chapter8.ExternalTensorFunctorLeft
import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.ComplexShapeSigns
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

set_option backward.isDefEq.respectTransparency false

/-!
# The external tensor complex of two projective resolutions (left modules)

Left-module twin of `ExternalTensorComplex.lean`. Building on the external-tensor bifunctor
`Etingof.extTensorFunctorLeft` (`Chapter8/ExternalTensorFunctorLeft.lean`), this file constructs,
from projective resolutions `P₁ : ProjectiveResolution (M₁ : ModuleCat A₁)` and
`P₂ : ProjectiveResolution (M₂ : ModuleCat A₂)` of **left** modules,

* `Etingof.extTensorComplexLeft P₁ P₂ : ChainComplex (ModuleCat (A₁ ⊗[k] A₂)) ℕ`, the total complex
  of the bicomplex `(j, m) ↦ extTensorFunctorLeft.obj (P₁.X j) |>.obj (P₂.X m)`;
* `Etingof.extTensorπL P₁ P₂ : extTensorComplexLeft P₁ P₂ ⟶ (single₀ _).obj (M₁ ⊗ M₂)`, the
  augmentation induced by `P₁.π ⊗ P₂.π`, nonzero only in degree 0.

As in the right-module case the total complex is Mathlib's `HomologicalComplex.mapBifunctor`.
-/

open CategoryTheory Limits MonoidalCategory HomologicalComplex TensorProduct

namespace Etingof

universe u

variable {k : Type u} [CommRing k]
variable {A₁ A₂ : Type u} [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]

attribute [local instance] restrictModule₁L restrictModule₂L tower₁L tower₂L extModuleL

section ZeroMorphisms

/-- The underlying linear map of `extTensorFunctorLeftMap` is zero when the first morphism is 0. -/
theorem extTensorFunctorLeftMapHom_zero_left {X X' : ModuleCat.{u} A₁} {Y Y' : ModuleCat.{u} A₂}
    (g : Y ⟶ Y') : extTensorFunctorLeftMapHom k (0 : X ⟶ X') g = 0 := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m₁ m₂ =>
    rw [extTensorFunctorLeftMapHom_tmul, ModuleCat.hom_zero, LinearMap.zero_apply, zero_tmul,
      LinearMap.zero_apply]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- `extTensorFunctorLeftMap` is zero when the first morphism is zero. -/
theorem extTensorFunctorLeftMap_zero_left {X X' : ModuleCat.{u} A₁} {Y Y' : ModuleCat.{u} A₂}
    (g : Y ⟶ Y') : extTensorFunctorLeftMap k (0 : X ⟶ X') g = 0 := by
  change ModuleCat.ofHom (extTensorFunctorLeftMapHom k (0 : X ⟶ X') g) = 0
  rw [extTensorFunctorLeftMapHom_zero_left, ModuleCat.ofHom_zero]

/-- The underlying linear map of `extTensorFunctorLeftMap` is zero when the second morphism is 0. -/
theorem extTensorFunctorLeftMapHom_zero_right {X X' : ModuleCat.{u} A₁} {Y Y' : ModuleCat.{u} A₂}
    (f : X ⟶ X') : extTensorFunctorLeftMapHom k f (0 : Y ⟶ Y') = 0 := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m₁ m₂ =>
    rw [extTensorFunctorLeftMapHom_tmul, ModuleCat.hom_zero, LinearMap.zero_apply, tmul_zero,
      LinearMap.zero_apply]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- `extTensorFunctorLeftMap` is zero when the second morphism is zero. -/
theorem extTensorFunctorLeftMap_zero_right {X X' : ModuleCat.{u} A₁} {Y Y' : ModuleCat.{u} A₂}
    (f : X ⟶ X') : extTensorFunctorLeftMap k f (0 : Y ⟶ Y') = 0 := by
  change ModuleCat.ofHom (extTensorFunctorLeftMapHom k f (0 : Y ⟶ Y')) = 0
  rw [extTensorFunctorLeftMapHom_zero_right, ModuleCat.ofHom_zero]

instance : (extTensorFunctorLeft k A₁ A₂).PreservesZeroMorphisms where
  map_zero X X' := by
    apply NatTrans.ext
    funext Y
    change extTensorFunctorLeftMap k (0 : X ⟶ X') (𝟙 Y) = 0
    exact extTensorFunctorLeftMap_zero_left (𝟙 Y)

instance (X : ModuleCat.{u} A₁) :
    ((extTensorFunctorLeft k A₁ A₂).obj X).PreservesZeroMorphisms where
  map_zero Y Y' := by
    change extTensorFunctorLeftMap k (𝟙 X) (0 : Y ⟶ Y') = 0
    exact extTensorFunctorLeftMap_zero_right (𝟙 X)

/-- The fibers of the total-degree map `(i₁, i₂) ↦ i₁ + i₂` on `ℕ × ℕ` are finite; needed for the
total complex `mapBifunctor … (down ℕ)` to have its degreewise coproducts. -/
instance extTensorComplexLeft_finite_fiber (n : ℕ) :
    Finite (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) ⁻¹' {n}) := by
  refine Finite.of_injective (fun ⟨⟨i₁, i₂⟩, (hi : i₁ + i₂ = n)⟩ =>
    ((⟨i₁, by omega⟩, ⟨i₂, by omega⟩) : Fin (n + 1) × Fin (n + 1))) ?_
  rintro ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ h
  simpa using h

end ZeroMorphisms

variable {M₁ : ModuleCat.{u} A₁} {M₂ : ModuleCat.{u} A₂}

/-- The **external tensor complex** of two projective resolutions of left modules: the total complex
of the bicomplex `(j, m) ↦ (P₁.complex.X j) ⊗[k] (P₂.complex.X m)` with its external
`A₁ ⊗[k] A₂`-action. -/
noncomputable abbrev extTensorComplexLeft
    (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂) :
    ChainComplex (ModuleCat.{u} (A₁ ⊗[k] A₂)) ℕ :=
  HomologicalComplex.mapBifunctor P₁.complex P₂.complex (extTensorFunctorLeft k A₁ A₂)
    (ComplexShape.down ℕ)

/-- The degree-0 component of the augmentation `extTensorπL`: on the only summand `(0, 0)` of
`(extTensorComplexLeft P₁ P₂).X 0` it is `(P₁.π)₀ ⊗ (P₂.π)₀ : (P₁)₀ ⊗ (P₂)₀ ⟶ M₁ ⊗ M₂`. -/
noncomputable abbrev extTensorAug₀L
    (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂) :
    (extTensorComplexLeft P₁ P₂).X 0 ⟶ extTensorFunctorLeftObj k A₁ A₂ M₁ M₂ :=
  HomologicalComplex.mapBifunctorDesc (j := 0) fun i₁ i₂ h =>
    match i₁, i₂, h with
    | 0, 0, _ =>
        ((extTensorFunctorLeft k A₁ A₂).map
            ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1).app
          (P₂.complex.X 0) ≫
        ((extTensorFunctorLeft k A₁ A₂).obj M₁).map
          ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).1
    | (_ + 1), _, h => absurd h (by simp)
    | 0, (_ + 1), h => absurd h (by simp)

/-- The augmentation commutes past the degree-1 differential. -/
theorem extTensorAug₀L_comm (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂) :
    (extTensorComplexLeft (k := k) P₁ P₂).d 1 0 ≫ extTensorAug₀L (k := k) P₁ P₂ = 0 := by
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
        (F := extTensorFunctorLeft k A₁ A₂) (c := ComplexShape.down ℕ) (i₁ := 1) (i₂ := 0) (j := 0)
        (by simp),
      HomologicalComplex.mapBifunctor.d₁_eq (K₁ := P₁.complex) (K₂ := P₂.complex)
        (F := extTensorFunctorLeft k A₁ A₂) (c := ComplexShape.down ℕ) (i₁ := 1) (i₁' := 0)
        (i₂ := 0) (j := 0) (h := by simp) (h' := by simp)]
    rw [zero_comp, add_zero,
      show ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) (1, 0) = 1 from rfl, one_smul, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc, ← NatTrans.comp_app_assoc, ← Functor.map_comp, hd₁]
    simp
  · rw [HomologicalComplex.mapBifunctor.d₁_eq_zero (K₁ := P₁.complex) (K₂ := P₂.complex)
        (F := extTensorFunctorLeft k A₁ A₂) (c := ComplexShape.down ℕ) (i₁ := 0) (i₂ := 1) (j := 0)
        (by simp),
      HomologicalComplex.mapBifunctor.d₂_eq (K₁ := P₁.complex) (K₂ := P₂.complex)
        (F := extTensorFunctorLeft k A₁ A₂) (c := ComplexShape.down ℕ) (i₁ := 0) (i₂ := 1)
        (i₂' := 0) (j := 0) (h := by simp) (h' := by simp)]
    rw [zero_comp, zero_add,
      show ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) (0, 1) = 1 from by simp [ComplexShape.ε₂, ComplexShape.ε],
      one_smul, Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
    dsimp only
    rw [((extTensorFunctorLeft k A₁ A₂).map ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1
        ).naturality_assoc, ← Functor.map_comp, hd₂]
    simp

/-- The **augmentation** of the external tensor complex: the chain map to `M₁ ⊗ M₂` concentrated in
degree 0, where it is `(P₁.π)₀ ⊗ (P₂.π)₀`. -/
noncomputable def extTensorπL
    (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂) :
    extTensorComplexLeft P₁ P₂ ⟶
      (ChainComplex.single₀ (ModuleCat.{u} (A₁ ⊗[k] A₂))).obj
        (extTensorFunctorLeftObj k A₁ A₂ M₁ M₂) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨extTensorAug₀L P₁ P₂, extTensorAug₀L_comm P₁ P₂⟩

end Etingof
