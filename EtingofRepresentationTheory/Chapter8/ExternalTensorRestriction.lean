import EtingofRepresentationTheory.Chapter8.ExternalTensorComplex
import EtingofRepresentationTheory.Chapter8.ExternalTensorProjective
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.Monoidal

set_option backward.isDefEq.respectTransparency false

/-!
# Restriction of scalars commutes with the external tensor complex

For projective resolutions `P₁ : ProjectiveResolution (M₁ : ModuleCat A₁ᵐᵒᵖ)` and
`P₂ : ProjectiveResolution (M₂ : ModuleCat A₂ᵐᵒᵖ)`, the external tensor complex
`Etingof.extTensorComplex P₁ P₂` is a `ChainComplex (ModuleCat (A₁ ⊗[k] A₂)ᵐᵒᵖ) ℕ`. To compute its
homology (needed for the `quasiIso` obligation of `extTensorProjectiveResolution`) we forget the
`(A₁ ⊗[k] A₂)ᵐᵒᵖ`-structure down to `ModuleCat k` along `algebraMap k (A₁ ⊗[k] A₂)ᵐᵒᵖ` and identify
the result with the plain `k`-tensor total complex of the underlying `k`-complexes of `P•₁`, `P•₂`.

The key point is a pointwise natural isomorphism of bifunctors: restricting the external
tensor `X ⊗[k] Y` (with its `(A₁ ⊗[k] A₂)ᵐᵒᵖ`-action) back to `k` recovers the plain `k`-tensor of
the two restricted modules.

* `Etingof.extRestrictObjIso`: for `X : ModuleCat A₁ᵐᵒᵖ`, `Y : ModuleCat A₂ᵐᵒᵖ`,
  `(restrictScalars (algebraMap k (A₁ ⊗[k] A₂)ᵐᵒᵖ)).obj (extTensorFunctorObj k A₁ A₂ X Y)
    ≅ (restrictScalars (algebraMap k A₁ᵐᵒᵖ)).obj X ⊗ (restrictScalars (algebraMap k A₂ᵐᵒᵖ)).obj Y`
  in `ModuleCat k`. The underlying map is the identity on `X ⊗[k] Y`; it is `k`-linear because the
  external action of `algebraMap k (A₁ ⊗[k] A₂)ᵐᵒᵖ c` is scalar multiplication by `c` (the external
  representation `extTensorRep` is a `k`-algebra map, so it sends `algebraMap` to `algebraMap`).
* `Etingof.extRestrictObjIso_naturality`: the identification is natural in `(X, Y)`.

## Construction

Building on the pointwise bifunctor isomorphism `extRestrictObjIso` and its naturality, this
file constructs the complex-level commutation isomorphism
`Etingof.extTensorComplex_restrictIso`:
`((restrictScalars (algebraMap k (A₁ ⊗[k] A₂)ᵐᵒᵖ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
(extTensorComplex P₁ P₂) ≅ HomologicalComplex.tensorObj (res₁Complex P₁) (res₂Complex P₂)` where
`res₁Complex P₁, res₂Complex P₂` are the restricted resolutions. The pointwise iso is transported
through the `mapBifunctor` total complex degreewise via `PreservesCoproduct.iso` (`restrictScalars`
preserves the degree-`n` coproduct, `preservesColimit_restrictScalars`) and `Sigma.mapIso`; the
Koszul-signed differential compatibility (`resExt_map_d₁_comp`, `resExt_map_d₂_comp`) reduces to
`extRestrictObjIso_naturality`. The degree-0 `π`-compatibility `ι_extRestrictComplexXIso_aug₀`
(the restricted augmentation corresponds to `res₁ (P₁.π)₀ ⊗ res₂ (P₂.π)₀`) is the map-level `i = 0`
square used by the `quasiIso` construction.
-/

open CategoryTheory Limits MonoidalCategory HomologicalComplex TensorProduct MulOpposite

namespace Etingof

universe u

variable {k : Type u} [CommRing k]
variable {A₁ A₂ : Type u} [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]

attribute [local instance] restrictModule₁ restrictModule₂ tower₁ tower₂ extModule

/-- Restriction of scalars along `k → (A₁ ⊗[k] A₂)ᵐᵒᵖ`. -/
noncomputable abbrev resExt (k A₁ A₂ : Type u) [CommRing k] [Ring A₁] [Ring A₂]
    [Algebra k A₁] [Algebra k A₂] :
    ModuleCat.{u} (A₁ ⊗[k] A₂)ᵐᵒᵖ ⥤ ModuleCat.{u} k :=
  ModuleCat.restrictScalars (algebraMap k (A₁ ⊗[k] A₂)ᵐᵒᵖ)

/-- Restriction of scalars along `k → A₁ᵐᵒᵖ`. -/
noncomputable abbrev res₁ (k A₁ : Type u) [CommRing k] [Ring A₁] [Algebra k A₁] :
    ModuleCat.{u} A₁ᵐᵒᵖ ⥤ ModuleCat.{u} k :=
  ModuleCat.restrictScalars (algebraMap k A₁ᵐᵒᵖ)

/-- Restriction of scalars along `k → A₂ᵐᵒᵖ`. -/
noncomputable abbrev res₂ (k A₂ : Type u) [CommRing k] [Ring A₂] [Algebra k A₂] :
    ModuleCat.{u} A₂ᵐᵒᵖ ⥤ ModuleCat.{u} k :=
  ModuleCat.restrictScalars (algebraMap k A₂ᵐᵒᵖ)

/-- The key pointwise fact: the external action of `algebraMap k (A₁ ⊗[k] A₂)ᵐᵒᵖ c` on `X ⊗[k] Y`
is scalar multiplication by `c`. Since `extTensorRep` is a `k`-algebra homomorphism, it sends
`algebraMap k (A₁ ⊗[k] A₂)ᵐᵒᵖ c` to `algebraMap k (Module.End k _) c = c • 𝟙`. -/
theorem extModule_algebraMap_smul (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ) (c : k)
    (z : X ⊗[k] Y) :
    (algebraMap k (A₁ ⊗[k] A₂)ᵐᵒᵖ c) • z = c • z := by
  change extTensorRep k A₁ A₂ X Y (algebraMap k (A₁ ⊗[k] A₂)ᵐᵒᵖ c) z = c • z
  rw [AlgHom.commutes]
  simp [Module.algebraMap_end_apply]

/-- The pointwise `k`-linear equivalence: restricting the external tensor `X ⊗[k] Y` to `k` gives
the plain `k`-tensor of the restricted modules. The underlying map is the identity on `X ⊗[k] Y`;
`k`-linearity is `extModule_algebraMap_smul`. -/
noncomputable def extRestrictObjEquiv (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    (resExt k A₁ A₂).obj (extTensorFunctorObj k A₁ A₂ X Y) ≃ₗ[k]
      ((res₁ k A₁).obj X) ⊗[k] ((res₂ k A₂).obj Y) where
  toFun z := z
  map_add' _ _ := rfl
  map_smul' c z := extModule_algebraMap_smul X Y c z
  invFun z := z
  left_inv _ := rfl
  right_inv _ := rfl

/-- The pointwise isomorphism in `ModuleCat k`:
`resExt (extTensorFunctorObj X Y) ≅ res₁ X ⊗ res₂ Y`. -/
noncomputable def extRestrictObjIso (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ) :
    (resExt k A₁ A₂).obj (extTensorFunctorObj k A₁ A₂ X Y) ≅
      ((res₁ k A₁).obj X) ⊗ ((res₂ k A₂).obj Y) :=
  (extRestrictObjEquiv X Y).toModuleIso

@[simp] theorem extRestrictObjIso_hom_tmul (X : ModuleCat.{u} A₁ᵐᵒᵖ) (Y : ModuleCat.{u} A₂ᵐᵒᵖ)
    (x : X) (y : Y) :
    (extRestrictObjIso X Y).hom (x ⊗ₜ[k] y) = x ⊗ₜ[k] y := rfl

/-- **Naturality of the pointwise iso.** The identification `extRestrictObjIso` intertwines the
restricted external-tensor functorial map `resExt (extTensorFunctorMap f g)` with the plain
`k`-tensor of the restricted maps `res₁ f ⊗ res₂ g`. Both underlying maps are `TensorProduct.map`
of the same `k`-linear factors, so the square commutes on simple tensors. -/
theorem extRestrictObjIso_naturality {X X' : ModuleCat.{u} A₁ᵐᵒᵖ} {Y Y' : ModuleCat.{u} A₂ᵐᵒᵖ}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (resExt k A₁ A₂).map (extTensorFunctorMap k f g) ≫ (extRestrictObjIso X' Y').hom =
      (extRestrictObjIso X Y).hom ≫
        MonoidalCategory.tensorHom ((res₁ k A₁).map f) ((res₂ k A₂).map g) := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb]

/-! ## The complex-level commutation isomorphism -/

variable {M₁ : ModuleCat.{u} A₁ᵐᵒᵖ} {M₂ : ModuleCat.{u} A₂ᵐᵒᵖ}

/-- The chain complex `P₁` of `A₁ᵐᵒᵖ`-modules restricted to a chain complex of `k`-modules. -/
noncomputable abbrev res₁Complex (P₁ : ProjectiveResolution M₁) :
    ChainComplex (ModuleCat.{u} k) ℕ :=
  ((res₁ k A₁).mapHomologicalComplex (ComplexShape.down ℕ)).obj P₁.complex

/-- The chain complex `P₂` of `A₂ᵐᵒᵖ`-modules restricted to a chain complex of `k`-modules. -/
noncomputable abbrev res₂Complex (P₂ : ProjectiveResolution M₂) :
    ChainComplex (ModuleCat.{u} k) ℕ :=
  ((res₂ k A₂).mapHomologicalComplex (ComplexShape.down ℕ)).obj P₂.complex

/-- The bicomplex `(i₁, i₂) ↦ (P₁.X i₁) ⊗[k] (P₂.X i₂)` (with the external
`(A₁ ⊗[k] A₂)ᵐᵒᵖ`-action) whose total complex is `extTensorComplex P₁ P₂`. -/
noncomputable abbrev extBicomplex (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂) :
    HomologicalComplex₂ (ModuleCat.{u} (A₁ ⊗[k] A₂)ᵐᵒᵖ)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (((extTensorFunctor k A₁ A₂).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj P₁.complex).obj P₂.complex

/-- The degreewise comparison isomorphism. In degree `n`, restricting the external tensor total
complex to `k` gives the `k`-tensor total complex of the restricted resolutions, because
`resExt` preserves the degree-`n` coproduct and matches summands via `extRestrictObjIso`. -/
noncomputable def extRestrictComplexXIso (P₁ : ProjectiveResolution M₁)
    (P₂ : ProjectiveResolution M₂) (n : ℕ) :
    (((resExt k A₁ A₂).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (extTensorComplex P₁ P₂)).X n ≅
      (HomologicalComplex.tensorObj (res₁Complex P₁) (res₂Complex P₂)).X n :=
  (PreservesCoproduct.iso (resExt k A₁ A₂)
    ((extBicomplex P₁ P₂).toGradedObject.mapObjFun
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)) n)) ≪≫
  Limits.Sigma.mapIso (fun i => extRestrictObjIso (P₁.complex.X i.1.1) (P₂.complex.X i.1.2))

/-- Summand behaviour of the inverse degreewise iso: the inclusion of the `(i₁, i₂)`-summand of
the `k`-tensor total complex, followed by `(extRestrictComplexXIso).inv`, is the pointwise inverse
iso followed by the restricted inclusion into the external tensor total complex. -/
theorem ι_extRestrictComplexXIso_inv (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂)
    (i₁ i₂ n : ℕ)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (i₁, i₂) = n) :
    ιMapBifunctor (res₁Complex P₁) (res₂Complex P₂) (curriedTensor (ModuleCat.{u} k))
        (ComplexShape.down ℕ) i₁ i₂ n h ≫ (extRestrictComplexXIso P₁ P₂ n).inv =
      (extRestrictObjIso (P₁.complex.X i₁) (P₂.complex.X i₂)).inv ≫ (resExt k A₁ A₂).map
        (ιMapBifunctor P₁.complex P₂.complex (extTensorFunctor k A₁ A₂) (ComplexShape.down ℕ)
          i₁ i₂ n h) := by
  simp only [extRestrictComplexXIso, Iso.trans_inv, PreservesCoproduct.inv_hom,
    HomologicalComplex.ιMapBifunctor, HomologicalComplex₂.ιTotal,
    CategoryTheory.GradedObject.ιMapObj, Limits.Sigma.ι_mapIso_inv_assoc,
    Limits.ι_comp_sigmaComparison]

/-- Summand behaviour of the forward degreewise iso (the hom-direction companion of
`ι_extRestrictComplexXIso_inv`). -/
theorem ι_extRestrictComplexXIso_hom (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂)
    (i₁ i₂ n : ℕ)
    (h : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (i₁, i₂) = n) :
    (resExt k A₁ A₂).map (ιMapBifunctor P₁.complex P₂.complex (extTensorFunctor k A₁ A₂)
        (ComplexShape.down ℕ) i₁ i₂ n h) ≫ (extRestrictComplexXIso P₁ P₂ n).hom =
      (extRestrictObjIso (P₁.complex.X i₁) (P₂.complex.X i₂)).hom ≫
        ιMapBifunctor (res₁Complex P₁) (res₂Complex P₂) (curriedTensor (ModuleCat.{u} k))
          (ComplexShape.down ℕ) i₁ i₂ n h := by
  rw [← cancel_mono (extRestrictComplexXIso P₁ P₂ n).inv, Category.assoc, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, ι_extRestrictComplexXIso_inv, ← Category.assoc,
    Iso.hom_inv_id, Category.id_comp]

/-- Compatibility of the degreewise iso with the first (Koszul-signed) differential: restricting the
`d₁` of the external tensor total complex and transporting along `extRestrictComplexXIso` recovers
the `d₁` of the `k`-tensor total complex. Reduces to `extRestrictObjIso_naturality` in the first
variable. -/
theorem resExt_map_d₁_comp (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂)
    (i₁ i₂ m : ℕ) :
    (resExt k A₁ A₂).map (HomologicalComplex.mapBifunctor.d₁ P₁.complex P₂.complex
        (extTensorFunctor k A₁ A₂) (ComplexShape.down ℕ) i₁ i₂ m) ≫
        (extRestrictComplexXIso P₁ P₂ m).hom =
      (extRestrictObjIso (P₁.complex.X i₁) (P₂.complex.X i₂)).hom ≫
        HomologicalComplex.mapBifunctor.d₁ (res₁Complex P₁) (res₂Complex P₂)
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
      rw [Functor.map_comp, Category.assoc, ι_extRestrictComplexXIso_hom,
        show ((extTensorFunctor k A₁ A₂).map (P₁.complex.d (i₁' + 1) i₁')).app
          (P₂.complex.X i₂) = extTensorFunctorMap k (P₁.complex.d (i₁' + 1) i₁')
            (𝟙 (P₂.complex.X i₂)) from rfl, ← Category.assoc,
        extRestrictObjIso_naturality, Category.assoc]
      congr 2
    · rw [HomologicalComplex.mapBifunctor.d₁_eq_zero' _ _ _ _
        (by simp [ComplexShape.down_Rel] : (ComplexShape.down ℕ).Rel (i₁' + 1) i₁') _ _ h',
        HomologicalComplex.mapBifunctor.d₁_eq_zero' _ _ _ _
        (by simp [ComplexShape.down_Rel] : (ComplexShape.down ℕ).Rel (i₁' + 1) i₁') _ _ h']
      simp

/-- Compatibility of the degreewise iso with the second differential. Reduces to
`extRestrictObjIso_naturality` in the second variable. -/
theorem resExt_map_d₂_comp (P₁ : ProjectiveResolution M₁) (P₂ : ProjectiveResolution M₂)
    (i₁ i₂ m : ℕ) :
    (resExt k A₁ A₂).map (HomologicalComplex.mapBifunctor.d₂ P₁.complex P₂.complex
        (extTensorFunctor k A₁ A₂) (ComplexShape.down ℕ) i₁ i₂ m) ≫
        (extRestrictComplexXIso P₁ P₂ m).hom =
      (extRestrictObjIso (P₁.complex.X i₁) (P₂.complex.X i₂)).hom ≫
        HomologicalComplex.mapBifunctor.d₂ (res₁Complex P₁) (res₂Complex P₂)
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
      rw [Functor.map_comp, Category.assoc, ι_extRestrictComplexXIso_hom,
        show ((extTensorFunctor k A₁ A₂).obj (P₁.complex.X i₁)).map (P₂.complex.d (i₂' + 1) i₂') =
          extTensorFunctorMap k (𝟙 (P₁.complex.X i₁)) (P₂.complex.d (i₂' + 1) i₂') from rfl,
        ← Category.assoc, extRestrictObjIso_naturality, Category.assoc]
      congr 2
    · rw [HomologicalComplex.mapBifunctor.d₂_eq_zero' _ _ _ _ _
        (by simp [ComplexShape.down_Rel] : (ComplexShape.down ℕ).Rel (i₂' + 1) i₂') _ h',
        HomologicalComplex.mapBifunctor.d₂_eq_zero' _ _ _ _ _
        (by simp [ComplexShape.down_Rel] : (ComplexShape.down ℕ).Rel (i₂' + 1) i₂') _ h']
      simp

/-- **The complex-level commutation isomorphism.** Restricting the external tensor complex of two
projective resolutions to `k` recovers the `k`-tensor total complex of the restricted resolutions.
This is the remaining half of Problem 8.2.8's restriction-of-scalars commutation, used
by the `quasiIso` construction. -/
noncomputable def extTensorComplex_restrictIso (P₁ : ProjectiveResolution M₁)
    (P₂ : ProjectiveResolution M₂) :
    ((resExt k A₁ A₂).mapHomologicalComplex (ComplexShape.down ℕ)).obj (extTensorComplex P₁ P₂) ≅
      HomologicalComplex.tensorObj (res₁Complex P₁) (res₂Complex P₂) :=
  HomologicalComplex.Hom.isoOfComponents (extRestrictComplexXIso P₁ P₂) <| by
    intro n m hnm
    rw [← cancel_epi (extRestrictComplexXIso P₁ P₂ n).inv, Iso.inv_hom_id_assoc]
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i₁ i₂ h
    -- Left-hand side: expand the target differential into `d₁_T + d₂_T`.
    rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂]
    -- Right-hand side: pull the summand injection through `isoN.inv` and the restricted
    -- differential, then expand into `resExt.map (d₁_ext + d₂_ext)`.
    rw [← Category.assoc _ (extRestrictComplexXIso P₁ P₂ n).inv, ι_extRestrictComplexXIso_inv,
      Category.assoc, Functor.mapHomologicalComplex_obj_d,
      ← Functor.map_comp_assoc,
      HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      Functor.map_add, Preadditive.add_comp, Preadditive.comp_add,
      resExt_map_d₁_comp, resExt_map_d₂_comp, ← Category.assoc, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp, Category.id_comp]

/-- **π-compatibility, degree 0.** On the only summand `(0, 0)` of degree 0, the restricted
augmentation `resExt (extTensorAug₀ P₁ P₂)`, transported along `extRestrictObjIso M₁ M₂`, is the
`k`-tensor `res₁ (P₁.π)₀ ⊗ res₂ (P₂.π)₀` of the restricted degree-0 augmentations. This is the
map-level `i = 0` square used by the `quasiIso` construction. Reduces to
`extRestrictObjIso_naturality` (and functoriality of `extTensorFunctorMap`). -/
theorem ι_extRestrictComplexXIso_aug₀ (P₁ : ProjectiveResolution M₁)
    (P₂ : ProjectiveResolution M₂)
    (h₀ : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (0, 0) = 0) :
    (resExt k A₁ A₂).map (ιMapBifunctor P₁.complex P₂.complex (extTensorFunctor k A₁ A₂)
        (ComplexShape.down ℕ) 0 0 0 h₀) ≫
        (resExt k A₁ A₂).map (extTensorAug₀ P₁ P₂) ≫ (extRestrictObjIso M₁ M₂).hom =
      (extRestrictObjIso (P₁.complex.X 0) (P₂.complex.X 0)).hom ≫ MonoidalCategory.tensorHom
        ((res₁ k A₁).map ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1)
        ((res₂ k A₂).map ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).1) := by
  rw [← Functor.map_comp_assoc, HomologicalComplex.ι_mapBifunctorDesc,
    show ((extTensorFunctor k A₁ A₂).map ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1).app
          (P₂.complex.X 0) ≫
        ((extTensorFunctor k A₁ A₂).obj M₁).map ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).1
      = extTensorFunctorMap k ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1
          ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).1 from by
        rw [show ((extTensorFunctor k A₁ A₂).map
              ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1).app (P₂.complex.X 0)
            = extTensorFunctorMap k ((ChainComplex.toSingle₀Equiv P₁.complex M₁) P₁.π).1
                (𝟙 (P₂.complex.X 0)) from rfl,
          show ((extTensorFunctor k A₁ A₂).obj M₁).map
              ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).1
            = extTensorFunctorMap k (𝟙 M₁) ((ChainComplex.toSingle₀Equiv P₂.complex M₂) P₂.π).1
                from rfl,
          ← extTensorFunctorMap_comp, Category.comp_id, Category.id_comp],
    extRestrictObjIso_naturality]

end Etingof
