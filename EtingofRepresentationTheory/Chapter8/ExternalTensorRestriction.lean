import EtingofRepresentationTheory.Chapter8.ExternalTensorComplex
import EtingofRepresentationTheory.Chapter8.ExternalTensorProjective
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.Monoidal

/-!
# Restriction of scalars commutes with the external tensor complex

For projective resolutions `P₁ : ProjectiveResolution (M₁ : ModuleCat A₁ᵐᵒᵖ)` and
`P₂ : ProjectiveResolution (M₂ : ModuleCat A₂ᵐᵒᵖ)`, the external tensor complex
`Etingof.extTensorComplex P₁ P₂` is a `ChainComplex (ModuleCat (A₁ ⊗[k] A₂)ᵐᵒᵖ) ℕ`. To compute its
homology (needed for the `quasiIso` obligation of `extTensorProjectiveResolution`) we forget the
`(A₁ ⊗[k] A₂)ᵐᵒᵖ`-structure down to `ModuleCat k` along `algebraMap k (A₁ ⊗[k] A₂)ᵐᵒᵖ` and identify
the result with the plain `k`-tensor total complex of the underlying `k`-complexes of `P•₁`, `P•₂`.

The geometric heart is a pointwise natural isomorphism of bifunctors: restricting the external
tensor `X ⊗[k] Y` (with its `(A₁ ⊗[k] A₂)ᵐᵒᵖ`-action) back to `k` recovers the plain `k`-tensor of
the two restricted modules.

* `Etingof.extRestrictObjIso`: for `X : ModuleCat A₁ᵐᵒᵖ`, `Y : ModuleCat A₂ᵐᵒᵖ`,
  `(restrictScalars (algebraMap k (A₁ ⊗[k] A₂)ᵐᵒᵖ)).obj (extTensorFunctorObj k A₁ A₂ X Y)
    ≅ (restrictScalars (algebraMap k A₁ᵐᵒᵖ)).obj X ⊗ (restrictScalars (algebraMap k A₂ᵐᵒᵖ)).obj Y`
  in `ModuleCat k`. The underlying map is the identity on `X ⊗[k] Y`; it is `k`-linear because the
  external action of `algebraMap k (A₁ ⊗[k] A₂)ᵐᵒᵖ c` is scalar multiplication by `c` (the external
  representation `extTensorRep` is a `k`-algebra map, so it sends `algebraMap` to `algebraMap`).
* `Etingof.extRestrictObjIso_naturality`: the identification is natural in `(X, Y)`.

## Status

This file currently delivers the **pointwise** bifunctor isomorphism and its naturality. The
**complex-level** commutation still to be assembled on top of it —
`(restrictScalars (algebraMap k (A₁ ⊗[k] A₂)ᵐᵒᵖ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
(extTensorComplex P₁ P₂) ≅ HomologicalComplex.tensorObj C₁ C₂` where `C₁, C₂` are the restricted
resolutions — requires transporting this pointwise iso through the `mapBifunctor` total complex,
i.e. that `restrictScalars` (which preserves coproducts, `preservesColimit_restrictScalars`)
commutes with the `GradedObject.mapObj` coproduct in each degree, matching the Koszul-signed
differentials. That assembly is tracked as follow-up work.
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

end Etingof
