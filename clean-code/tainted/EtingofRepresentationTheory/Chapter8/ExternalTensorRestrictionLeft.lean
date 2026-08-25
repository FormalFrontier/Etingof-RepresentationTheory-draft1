import EtingofRepresentationTheory.Chapter8.ExternalTensorComplexLeft
import EtingofRepresentationTheory.Chapter8.ExternalTensorProjectiveLeft
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.Monoidal

set_option backward.isDefEq.respectTransparency false

/-!
# Restriction of scalars commutes with the external tensor complex (left modules)

Left-module twin of `ExternalTensorRestriction.lean`. For projective resolutions
`P₁ : ProjectiveResolution (M₁ : ModuleCat A₁)` and `P₂ : ProjectiveResolution (M₂ : ModuleCat A₂)`
of left modules, the external tensor complex `Etingof.extTensorComplexLeft P₁ P₂` is a
`ChainComplex (ModuleCat (A₁ ⊗[k] A₂)) ℕ`. To compute its homology we forget the
`A₁ ⊗[k] A₂`-structure down to `ModuleCat k` and identify the result with the plain `k`-tensor total
complex of the underlying `k`-complexes of `P•₁`, `P•₂`.

* `Etingof.extRestrictObjIsoL`: the pointwise identification, underlying map the identity on
  `X ⊗[k] Y`, `k`-linear because the external action of `algebraMap k (A₁ ⊗[k] A₂) c` is scalar
  multiplication by `c`.
* `Etingof.extTensorComplexLeft_restrictIso`: the complex-level commutation isomorphism.
* `Etingof.ι_extRestrictComplexXIsoL_aug₀`: the degree-0 `π`-compatibility square.
-/

open CategoryTheory Limits MonoidalCategory HomologicalComplex TensorProduct

namespace Etingof

universe u

variable {k : Type u} [CommRing k]
variable {A₁ A₂ : Type u} [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]

attribute [local instance] restrictModule₁L restrictModule₂L tower₁L tower₂L extModuleL

/-- Restriction of scalars along `k → A₁ ⊗[k] A₂`. -/
noncomputable abbrev resExtL (k A₁ A₂ : Type u) [CommRing k] [Ring A₁] [Ring A₂]
    [Algebra k A₁] [Algebra k A₂] :
    ModuleCat.{u} (A₁ ⊗[k] A₂) ⥤ ModuleCat.{u} k :=
  ModuleCat.restrictScalars (algebraMap k (A₁ ⊗[k] A₂))

/-- Restriction of scalars along `k → A₁`. -/
noncomputable abbrev res₁L (k A₁ : Type u) [CommRing k] [Ring A₁] [Algebra k A₁] :
    ModuleCat.{u} A₁ ⥤ ModuleCat.{u} k :=
  ModuleCat.restrictScalars (algebraMap k A₁)

/-- Restriction of scalars along `k → A₂`. -/
noncomputable abbrev res₂L (k A₂ : Type u) [CommRing k] [Ring A₂] [Algebra k A₂] :
    ModuleCat.{u} A₂ ⥤ ModuleCat.{u} k :=
  ModuleCat.restrictScalars (algebraMap k A₂)

/-- The key pointwise fact: the external action of `algebraMap k (A₁ ⊗[k] A₂) c` on `X ⊗[k] Y` is
scalar multiplication by `c`. Since `extTensorRepLeft` is a `k`-algebra homomorphism, it sends
`algebraMap k (A₁ ⊗[k] A₂) c` to `algebraMap k (Module.End k _) c = c • 𝟙`. -/
theorem extModuleL_algebraMap_smul (X : ModuleCat.{u} A₁) (Y : ModuleCat.{u} A₂) (c : k)
    (z : X ⊗[k] Y) :
    (algebraMap k (A₁ ⊗[k] A₂) c) • z = c • z := by
  change extTensorRepLeft k A₁ A₂ X Y (algebraMap k (A₁ ⊗[k] A₂) c) z = c • z
  rw [AlgHom.commutes]
  simp [Module.algebraMap_end_apply]

/-- The pointwise `k`-linear equivalence: restricting the external tensor `X ⊗[k] Y` to `k` gives
the plain `k`-tensor of the restricted modules. -/
noncomputable def extRestrictObjEquivL (X : ModuleCat.{u} A₁) (Y : ModuleCat.{u} A₂) :
    (resExtL k A₁ A₂).obj (extTensorFunctorLeftObj k A₁ A₂ X Y) ≃ₗ[k]
      ((res₁L k A₁).obj X) ⊗[k] ((res₂L k A₂).obj Y) where
  toFun z := z
  map_add' _ _ := rfl
  map_smul' c z := extModuleL_algebraMap_smul X Y c z
  invFun z := z
  left_inv _ := rfl
  right_inv _ := rfl

/-- The pointwise isomorphism in `ModuleCat k`:
`resExtL (extTensorFunctorLeftObj X Y) ≅ res₁L X ⊗ res₂L Y`. -/
noncomputable def extRestrictObjIsoL (X : ModuleCat.{u} A₁) (Y : ModuleCat.{u} A₂) :
    (resExtL k A₁ A₂).obj (extTensorFunctorLeftObj k A₁ A₂ X Y) ≅
      ((res₁L k A₁).obj X) ⊗ ((res₂L k A₂).obj Y) :=
  (extRestrictObjEquivL X Y).toModuleIso

@[simp] theorem extRestrictObjIsoL_hom_tmul (X : ModuleCat.{u} A₁) (Y : ModuleCat.{u} A₂)
    (x : X) (y : Y) :
    (extRestrictObjIsoL X Y).hom (x ⊗ₜ[k] y) = x ⊗ₜ[k] y := rfl

/-- **Naturality of the pointwise iso.** -/
theorem extRestrictObjIsoL_naturality {X X' : ModuleCat.{u} A₁} {Y Y' : ModuleCat.{u} A₂}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (resExtL k A₁ A₂).map (extTensorFunctorLeftMap k f g) ≫ (extRestrictObjIsoL X' Y').hom =
      (extRestrictObjIsoL X Y).hom ≫
        MonoidalCategory.tensorHom ((res₁L k A₁).map f) ((res₂L k A₂).map g) := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb]

/-! ## The complex-level commutation isomorphism -/

variable {M₁ : ModuleCat.{u} A₁} {M₂ : ModuleCat.{u} A₂}

/-- The chain complex `P₁` of `A₁`-modules restricted to a chain complex of `k`-modules. -/
noncomputable abbrev res₁ComplexL (P₁ : ProjectiveResolution M₁) :
    ChainComplex (ModuleCat.{u} k) ℕ :=
  ((res₁L k A₁).mapHomologicalComplex (ComplexShape.down ℕ)).obj P₁.complex

/-- The chain complex `P₂` of `A₂`-modules restricted to a chain complex of `k`-modules. -/
noncomputable abbrev res₂ComplexL (P₂ : ProjectiveResolution M₂) :
    ChainComplex (ModuleCat.{u} k) ℕ :=
  ((res₂L k A₂).mapHomologicalComplex (ComplexShape.down ℕ)).obj P₂.complex

/-- The bicomplex `(i₁, i₂) ↦ (P₁.X i₁) ⊗[k] (P₂.X i₂)` (with the external `A₁ ⊗[k] A₂`-action)
whose total complex is `extTensorComplexLeft P₁ P₂`. -/
noncomputable abbrev extBicomplexL (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂) :
    HomologicalComplex₂ (ModuleCat.{u} (A₁ ⊗[k] A₂))
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (((extTensorFunctorLeft k A₁ A₂).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj P₁.complex).obj P₂.complex

/-- The degreewise comparison isomorphism. -/
noncomputable def extRestrictComplexXIsoL (P₁ : ProjectiveResolution M₁)
    (P₂ : ProjectiveResolution M₂) (n : ℕ) :
    (((resExtL k A₁ A₂).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (extTensorComplexLeft P₁ P₂)).X n ≅
      (HomologicalComplex.tensorObj (res₁ComplexL P₁) (res₂ComplexL P₂)).X n :=
  (PreservesCoproduct.iso (resExtL k A₁ A₂)
    ((extBicomplexL P₁ P₂).toGradedObject.mapObjFun
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)) n)) ≪≫
  Limits.Sigma.mapIso (fun i => extRestrictObjIsoL (P₁.complex.X i.1.1) (P₂.complex.X i.1.2))

/-- Summand behaviour of the inverse degreewise iso. -/
theorem ι_extRestrictComplexXIsoL_inv (P₁ : ProjectiveResolution M₁)
    (P₂ : ProjectiveResolution M₂) (i₁ i₂ n : ℕ)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (i₁, i₂) = n) :
    ιMapBifunctor (res₁ComplexL P₁) (res₂ComplexL P₂) (curriedTensor (ModuleCat.{u} k))
        (ComplexShape.down ℕ) i₁ i₂ n h ≫ (extRestrictComplexXIsoL P₁ P₂ n).inv =
      (extRestrictObjIsoL (P₁.complex.X i₁) (P₂.complex.X i₂)).inv ≫ (resExtL k A₁ A₂).map
        (ιMapBifunctor P₁.complex P₂.complex (extTensorFunctorLeft k A₁ A₂) (ComplexShape.down ℕ)
          i₁ i₂ n h) := by
  simp only [extRestrictComplexXIsoL, Iso.trans_inv, PreservesCoproduct.inv_hom,
    HomologicalComplex.ιMapBifunctor, HomologicalComplex₂.ιTotal,
    CategoryTheory.GradedObject.ιMapObj, Limits.Sigma.ι_mapIso_inv_assoc,
    Limits.ι_comp_sigmaComparison]

/-- Summand behaviour of the forward degreewise iso. -/
theorem ι_extRestrictComplexXIsoL_hom (P₁ : ProjectiveResolution M₁)
    (P₂ : ProjectiveResolution M₂) (i₁ i₂ n : ℕ)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (i₁, i₂) = n) :
    (resExtL k A₁ A₂).map (ιMapBifunctor P₁.complex P₂.complex (extTensorFunctorLeft k A₁ A₂)
        (ComplexShape.down ℕ) i₁ i₂ n h) ≫ (extRestrictComplexXIsoL P₁ P₂ n).hom =
      (extRestrictObjIsoL (P₁.complex.X i₁) (P₂.complex.X i₂)).hom ≫
        ιMapBifunctor (res₁ComplexL P₁) (res₂ComplexL P₂) (curriedTensor (ModuleCat.{u} k))
          (ComplexShape.down ℕ) i₁ i₂ n h := by
  rw [← cancel_mono (extRestrictComplexXIsoL P₁ P₂ n).inv, Category.assoc, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, ι_extRestrictComplexXIsoL_inv, ← Category.assoc,
    Iso.hom_inv_id, Category.id_comp]

/-- Compatibility of the degreewise iso with the first (Koszul-signed) differential. -/
theorem resExtL_map_d₁_comp (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂)
    (i₁ i₂ m : ℕ) :
    (resExtL k A₁ A₂).map (HomologicalComplex.mapBifunctor.d₁ P₁.complex P₂.complex
        (extTensorFunctorLeft k A₁ A₂) (ComplexShape.down ℕ) i₁ i₂ m) ≫
        (extRestrictComplexXIsoL P₁ P₂ m).hom =
      (extRestrictObjIsoL (P₁.complex.X i₁) (P₂.complex.X i₂)).hom ≫
        HomologicalComplex.mapBifunctor.d₁ (res₁ComplexL P₁) (res₂ComplexL P₂)
          (curriedTensor (ModuleCat.{u} k)) (ComplexShape.down ℕ) i₁ i₂ m := by
  rcases i₁ with _ | i₁'
  · rw [HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _
        (by rw [ChainComplex.next_nat_zero]; simp [ComplexShape.down_Rel]),
      HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _
        (by rw [ChainComplex.next_nat_zero]; simp [ComplexShape.down_Rel])]
    simp
  · by_cases h' : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (i₁', i₂) = m
    · rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (by simp [ComplexShape.down_Rel]) _ _ h',
        HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (by simp [ComplexShape.down_Rel]) _ _ h',
        Functor.map_units_smul, Linear.units_smul_comp, Linear.comp_units_smul]
      congr 1
      rw [Functor.map_comp, Category.assoc, ι_extRestrictComplexXIsoL_hom,
        show ((extTensorFunctorLeft k A₁ A₂).map (P₁.complex.d (i₁' + 1) i₁')).app
          (P₂.complex.X i₂) = extTensorFunctorLeftMap k (P₁.complex.d (i₁' + 1) i₁')
            (𝟙 (P₂.complex.X i₂)) from rfl, ← Category.assoc,
        extRestrictObjIsoL_naturality, Category.assoc]
      congr 2
    · rw [HomologicalComplex.mapBifunctor.d₁_eq_zero' _ _ _ _
        (by simp [ComplexShape.down_Rel] : (ComplexShape.down ℕ).Rel (i₁' + 1) i₁') _ _ h',
        HomologicalComplex.mapBifunctor.d₁_eq_zero' _ _ _ _
        (by simp [ComplexShape.down_Rel] : (ComplexShape.down ℕ).Rel (i₁' + 1) i₁') _ _ h']
      simp

/-- Compatibility of the degreewise iso with the second differential. -/
theorem resExtL_map_d₂_comp (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂)
    (i₁ i₂ m : ℕ) :
    (resExtL k A₁ A₂).map (HomologicalComplex.mapBifunctor.d₂ P₁.complex P₂.complex
        (extTensorFunctorLeft k A₁ A₂) (ComplexShape.down ℕ) i₁ i₂ m) ≫
        (extRestrictComplexXIsoL P₁ P₂ m).hom =
      (extRestrictObjIsoL (P₁.complex.X i₁) (P₂.complex.X i₂)).hom ≫
        HomologicalComplex.mapBifunctor.d₂ (res₁ComplexL P₁) (res₂ComplexL P₂)
          (curriedTensor (ModuleCat.{u} k)) (ComplexShape.down ℕ) i₁ i₂ m := by
  rcases i₂ with _ | i₂'
  · rw [HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _
        (by rw [ChainComplex.next_nat_zero]; simp [ComplexShape.down_Rel]),
      HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _
        (by rw [ChainComplex.next_nat_zero]; simp [ComplexShape.down_Rel])]
    simp
  · by_cases h' : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (i₁, i₂') = m
    · rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ (by simp [ComplexShape.down_Rel]) _ h',
        HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ (by simp [ComplexShape.down_Rel]) _ h',
        Functor.map_units_smul, Linear.units_smul_comp, Linear.comp_units_smul]
      congr 1
      rw [Functor.map_comp, Category.assoc, ι_extRestrictComplexXIsoL_hom,
        show ((extTensorFunctorLeft k A₁ A₂).obj (P₁.complex.X i₁)).map
            (P₂.complex.d (i₂' + 1) i₂') =
          extTensorFunctorLeftMap k (𝟙 (P₁.complex.X i₁)) (P₂.complex.d (i₂' + 1) i₂') from rfl,
        ← Category.assoc, extRestrictObjIsoL_naturality, Category.assoc]
      congr 2
    · rw [HomologicalComplex.mapBifunctor.d₂_eq_zero' _ _ _ _ _
        (by simp [ComplexShape.down_Rel] : (ComplexShape.down ℕ).Rel (i₂' + 1) i₂') _ h',
        HomologicalComplex.mapBifunctor.d₂_eq_zero' _ _ _ _ _
        (by simp [ComplexShape.down_Rel] : (ComplexShape.down ℕ).Rel (i₂' + 1) i₂') _ h']
      simp

/-- **The complex-level commutation isomorphism.** Restricting the external tensor complex of two
projective resolutions to `k` recovers the `k`-tensor total complex of the restricted
resolutions. -/
noncomputable def extTensorComplexLeft_restrictIso (P₁ : ProjectiveResolution M₁)
    (P₂ : ProjectiveResolution M₂) :
    ((resExtL k A₁ A₂).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (extTensorComplexLeft P₁ P₂) ≅
      HomologicalComplex.tensorObj (res₁ComplexL P₁) (res₂ComplexL P₂) :=
  HomologicalComplex.Hom.isoOfComponents (extRestrictComplexXIsoL P₁ P₂) <| by
    intro n m hnm
    rw [← cancel_epi (extRestrictComplexXIsoL P₁ P₂ n).inv, Iso.inv_hom_id_assoc]
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i₁ i₂ h
    rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂]
    rw [← Category.assoc _ (extRestrictComplexXIsoL P₁ P₂ n).inv, ι_extRestrictComplexXIsoL_inv,
      Category.assoc, Functor.mapHomologicalComplex_obj_d,
      ← Functor.map_comp_assoc,
      HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      Functor.map_add, Preadditive.add_comp, Preadditive.comp_add,
      resExtL_map_d₁_comp, resExtL_map_d₂_comp, ← Category.assoc, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp, Category.id_comp]

/-- **π-compatibility, degree 0.** -/
theorem ι_extRestrictComplexXIsoL_aug₀ (P₁ : ProjectiveResolution M₁)
    (P₂ : ProjectiveResolution M₂)
    (h₀ : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (0, 0) = 0) :
    (resExtL k A₁ A₂).map (ιMapBifunctor P₁.complex P₂.complex (extTensorFunctorLeft k A₁ A₂)
        (ComplexShape.down ℕ) 0 0 0 h₀) ≫
        (resExtL k A₁ A₂).map (extTensorAug₀L P₁ P₂) ≫ (extRestrictObjIsoL M₁ M₂).hom =
      (extRestrictObjIsoL (P₁.complex.X 0) (P₂.complex.X 0)).hom ≫ MonoidalCategory.tensorHom
        ((res₁L k A₁).map ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1)
        ((res₂L k A₂).map ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).1) := by
  rw [← Functor.map_comp_assoc, HomologicalComplex.ι_mapBifunctorDesc,
    show ((extTensorFunctorLeft k A₁ A₂).map
          ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1).app (P₂.complex.X 0) ≫
        ((extTensorFunctorLeft k A₁ A₂).obj M₁).map
          ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).1
      = extTensorFunctorLeftMap k ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1
          ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).1 from by
        rw [show ((extTensorFunctorLeft k A₁ A₂).map
              ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1).app (P₂.complex.X 0)
            = extTensorFunctorLeftMap k ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1
                (𝟙 (P₂.complex.X 0)) from rfl,
          show ((extTensorFunctorLeft k A₁ A₂).obj M₁).map
              ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).1
            = extTensorFunctorLeftMap k (𝟙 M₁) ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).1
                from rfl,
          ← extTensorFunctorLeftMap_comp, Category.comp_id, Category.id_comp],
    extRestrictObjIsoL_naturality]

end Etingof
