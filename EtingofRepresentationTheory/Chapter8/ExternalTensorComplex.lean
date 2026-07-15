import EtingofRepresentationTheory.Chapter8.ExternalTensorFunctor
import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.ComplexShapeSigns
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

/-!
# The external tensor complex of two projective resolutions

Building on the external-tensor bifunctor `Etingof.extTensorFunctor`
(`Chapter8/ExternalTensorFunctor.lean`), this file constructs, from projective resolutions
`P₁ : ProjectiveResolution (M₁ : ModuleCat A₁ᵐᵒᵖ)` and
`P₂ : ProjectiveResolution (M₂ : ModuleCat A₂ᵐᵒᵖ)`,

* `Etingof.extTensorComplex P₁ P₂ : ChainComplex (ModuleCat (A₁ ⊗[k] A₂)ᵐᵒᵖ) ℕ`, the total complex
  of the bicomplex `(j, m) ↦ extTensorFunctor.obj (P₁.X j) |>.obj (P₂.X m)`. Degree `i` is
  `⨁_{j+m=i} (P₁.complex.X j) ⊗[k] (P₂.complex.X m)` with the Koszul-signed differential
  `d₁ ⊗ 1 + (-1)ʲ · 1 ⊗ d₂` (the sign is `ComplexShape.ε₂` of the diagonal
  `TotalComplexShape (down ℕ) (down ℕ) (down ℕ)`, namely `(-1) ^ j`);
* `Etingof.extTensorπ P₁ P₂ : extTensorComplex P₁ P₂ ⟶ (single₀ _).obj (M₁ ⊗ M₂)`, the augmentation
  induced by `P₁.π ⊗ P₂.π`, nonzero only in degree 0 where it is `π₁₀ ⊗ π₂₀`.

The total complex is Mathlib's `HomologicalComplex.mapBifunctor`, which supplies the differential
(with signs), `d_comp_d`, and the summand API (`ιMapBifunctor`, `mapBifunctorDesc`). This issue is
purely the complex + augmentation data; projectivity and exactness are handled elsewhere.
-/

open CategoryTheory Limits MonoidalCategory HomologicalComplex TensorProduct MulOpposite

namespace Etingof

universe u

variable {k : Type u} [CommRing k]
variable {A₁ A₂ : Type u} [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]

section ZeroMorphisms

-- The same restriction-of-scalars and external-action `local instance`s as in
-- `ExternalTensorFunctor.lean`, brought into scope so that the `Module` instance packaged by
-- `extTensorFunctorObj` is *definitionally the one* used by `extTensorFunctorMapHom`. Without this,
-- LinearMap-level rewrites against `extTensorFunctorMapHom` fail on an instance diamond.
noncomputable local instance (X : ModuleCat.{u} A₁ᵐᵒᵖ) : Module k X :=
  Module.compHom X (algebraMap k A₁ᵐᵒᵖ)

noncomputable local instance (Y : ModuleCat.{u} A₂ᵐᵒᵖ) : Module k Y :=
  Module.compHom Y (algebraMap k A₂ᵐᵒᵖ)

local instance (X : ModuleCat.{u} A₁ᵐᵒᵖ) : IsScalarTower k A₁ᵐᵒᵖ X :=
  { smul_assoc := fun a b x => by rw [Algebra.smul_def]; exact mul_smul _ _ _ }

local instance (Y : ModuleCat.{u} A₂ᵐᵒᵖ) : IsScalarTower k A₂ᵐᵒᵖ Y :=
  { smul_assoc := fun a b x => by rw [Algebra.smul_def]; exact mul_smul _ _ _ }

noncomputable local instance (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    Module (A₁ ⊗[k] A₂)ᵐᵒᵖ (X ⊗[k] Y) := extTensorModule k A₁ A₂ X Y

/-- The underlying linear map of `extTensorFunctorMap` is zero when the first morphism is zero. -/
theorem extTensorFunctorMapHom_zero_left {X X' : ModuleCat.{u} A₁ᵐᵒᵖ} {Y Y' : ModuleCat.{u} A₂ᵐᵒᵖ}
    (g : Y ⟶ Y') : extTensorFunctorMapHom k (0 : X ⟶ X') g = 0 := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m₁ m₂ =>
    rw [extTensorFunctorMapHom_tmul, ModuleCat.hom_zero, LinearMap.zero_apply, zero_tmul,
      LinearMap.zero_apply]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- `extTensorFunctorMap` is zero when the first morphism is zero. -/
theorem extTensorFunctorMap_zero_left {X X' : ModuleCat.{u} A₁ᵐᵒᵖ} {Y Y' : ModuleCat.{u} A₂ᵐᵒᵖ}
    (g : Y ⟶ Y') : extTensorFunctorMap k (0 : X ⟶ X') g = 0 := by
  change ModuleCat.ofHom (extTensorFunctorMapHom k (0 : X ⟶ X') g) = 0
  rw [extTensorFunctorMapHom_zero_left, ModuleCat.ofHom_zero]

/-- The underlying linear map of `extTensorFunctorMap` is zero when the second morphism is zero. -/
theorem extTensorFunctorMapHom_zero_right {X X' : ModuleCat.{u} A₁ᵐᵒᵖ} {Y Y' : ModuleCat.{u} A₂ᵐᵒᵖ}
    (f : X ⟶ X') : extTensorFunctorMapHom k f (0 : Y ⟶ Y') = 0 := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul m₁ m₂ =>
    rw [extTensorFunctorMapHom_tmul, ModuleCat.hom_zero, LinearMap.zero_apply, tmul_zero,
      LinearMap.zero_apply]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- `extTensorFunctorMap` is zero when the second morphism is zero. -/
theorem extTensorFunctorMap_zero_right {X X' : ModuleCat.{u} A₁ᵐᵒᵖ} {Y Y' : ModuleCat.{u} A₂ᵐᵒᵖ}
    (f : X ⟶ X') : extTensorFunctorMap k f (0 : Y ⟶ Y') = 0 := by
  change ModuleCat.ofHom (extTensorFunctorMapHom k f (0 : Y ⟶ Y')) = 0
  rw [extTensorFunctorMapHom_zero_right, ModuleCat.ofHom_zero]

instance : (extTensorFunctor k A₁ A₂).PreservesZeroMorphisms where
  map_zero X X' := by
    apply NatTrans.ext
    funext Y
    change extTensorFunctorMap k (0 : X ⟶ X') (𝟙 Y) = 0
    exact extTensorFunctorMap_zero_left (𝟙 Y)

instance (X : ModuleCat.{u} A₁ᵐᵒᵖ) : ((extTensorFunctor k A₁ A₂).obj X).PreservesZeroMorphisms where
  map_zero Y Y' := by
    change extTensorFunctorMap k (𝟙 X) (0 : Y ⟶ Y') = 0
    exact extTensorFunctorMap_zero_right (𝟙 X)

/-- The fibers of the total-degree map `(i₁, i₂) ↦ i₁ + i₂` on `ℕ × ℕ` are finite; needed for the
total complex `mapBifunctor … (down ℕ)` to have its degreewise coproducts. Phrased for the
`ComplexShape.π` of the diagonal `TotalComplexShape (down ℕ) (down ℕ) (down ℕ)` so typeclass search
picks it up when forming `extTensorComplex`. -/
instance extTensorComplex_finite_fiber (n : ℕ) :
    Finite (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) ⁻¹' {n}) := by
  refine Finite.of_injective (fun ⟨⟨i₁, i₂⟩, (hi : i₁ + i₂ = n)⟩ =>
    ((⟨i₁, by omega⟩, ⟨i₂, by omega⟩) : Fin (n + 1) × Fin (n + 1))) ?_
  rintro ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ h
  simpa using h

end ZeroMorphisms

variable {M₁ : ModuleCat.{u} A₁ᵐᵒᵖ} {M₂ : ModuleCat.{u} A₂ᵐᵒᵖ}

/-- The **external tensor complex** of two projective resolutions: the total complex of the
bicomplex `(j, m) ↦ (P₁.complex.X j) ⊗[k] (P₂.complex.X m)` with its external
`(A₁ ⊗[k] A₂)ᵐᵒᵖ`-action, differential `d₁ ⊗ 1 + (-1)ʲ · 1 ⊗ d₂`. -/
noncomputable def extTensorComplex
    (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂) :
    ChainComplex (ModuleCat.{u} (A₁ ⊗[k] A₂)ᵐᵒᵖ) ℕ :=
  HomologicalComplex.mapBifunctor P₁.complex P₂.complex (extTensorFunctor k A₁ A₂)
    (ComplexShape.down ℕ)

end Etingof
